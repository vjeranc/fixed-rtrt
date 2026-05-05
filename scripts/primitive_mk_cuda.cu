#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include <cuda_runtime.h>

namespace {

using Word = unsigned __int128;
using Count = uint64_t;

static constexpr int MAX_N = 64;
static constexpr Word LEAF = static_cast<Word>(2);

__constant__ Count c_nonleaf[MAX_N + 1];
__constant__ Count c_blocks[MAX_N + 1];

struct MatchTable {
  uint8_t close[128];
};

struct Row {
  unsigned long long fixed_points;
  unsigned long long fixed_orbits;
  unsigned long long exact_points;
  unsigned long long exact_orbits;
  float kernel_ms;
  std::vector<Word> orbit_reps;
};

uint64_t reverse64(uint64_t x) {
  x = ((x & 0x5555555555555555ULL) << 1) | ((x >> 1) & 0x5555555555555555ULL);
  x = ((x & 0x3333333333333333ULL) << 2) | ((x >> 2) & 0x3333333333333333ULL);
  x = ((x & 0x0F0F0F0F0F0F0F0FULL) << 4) | ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL);
  x = ((x & 0x00FF00FF00FF00FFULL) << 8) | ((x >> 8) & 0x00FF00FF00FF00FFULL);
  x = ((x & 0x0000FFFF0000FFFFULL) << 16) | ((x >> 16) & 0x0000FFFF0000FFFFULL);
  x = (x << 32) | (x >> 32);
  return x;
}

Word reverse128(Word x) {
  uint64_t lo = static_cast<uint64_t>(x);
  uint64_t hi = static_cast<uint64_t>(x >> 64);
  return (static_cast<Word>(reverse64(lo)) << 64) | static_cast<Word>(reverse64(hi));
}

Word low_mask(int len) {
  return (len == 128) ? ~static_cast<Word>(0) : ((static_cast<Word>(1) << len) - 1);
}

int bit_at(Word word, int total_len, int pos) {
  return static_cast<int>((word >> (total_len - 1 - pos)) & static_cast<Word>(1));
}

Word revcomp_bp(Word word, int len) {
  if (len == 0) return 0;
  Word rev = reverse128(word) >> (128 - len);
  return (~rev) & low_mask(len);
}

std::string to_string_bp(Word word, int total_len) {
  std::string out;
  out.reserve(total_len);
  for (int i = 0; i < total_len; ++i) out.push_back(bit_at(word, total_len, i) ? '(' : ')');
  return out;
}

MatchTable build_match(Word word, int len) {
  MatchTable mt{};
  int stack[128];
  int top = 0;
  for (int i = 0; i < len; ++i) {
    if (bit_at(word, len, i)) stack[top++] = i;
    else mt.close[stack[--top]] = static_cast<uint8_t>(i);
  }
  return mt;
}

void t_emit_rec(const MatchTable& mt, int l, int r, Word& out) {
  if (l >= r) return;
  int m = mt.close[l];
  out = (out << 1) | static_cast<Word>(1);
  t_emit_rec(mt, m + 1, r, out);
  out <<= 1;
  t_emit_rec(mt, l + 1, m, out);
}

Word T_bp(Word word, int len) {
  MatchTable mt = build_match(word, len);
  Word out = 0;
  t_emit_rec(mt, 0, len, out);
  return out;
}

Word M_bp(Word word, int len) {
  return T_bp(revcomp_bp(word, len), len);
}

inline Word concat_bp(Word left, int left_nodes, Word right, int right_nodes) {
  (void)left_nodes;
  return (left << (2 * right_nodes)) | right;
}

inline Word make_tree(Word child, int child_nodes) {
  Word w = static_cast<Word>(1);
  w = (w << (2 * child_nodes)) | child;
  w <<= 1;
  return w;
}

void build_counts(
    int max_n,
    std::vector<Count>& nonleaf,
    std::vector<Count>& blocks,
    std::vector<Count>& forests,
    std::vector<Count>& centers,
    std::vector<Count>& rfixed) {
  nonleaf.assign(max_n + 1, 0);
  blocks.assign(max_n + 1, 0);
  forests.assign(max_n + 1, 0);
  centers.assign(max_n + 1, 0);
  rfixed.assign(max_n + 1, 0);

  forests[0] = 1;
  forests[1] = 1;
  if (max_n >= 2) {
    forests[2] = 2;
    nonleaf[2] = 1;
    blocks[0] = 1;
    centers[2] = 1;
    rfixed[0] = 1;
    rfixed[1] = 1;
    rfixed[2] = 2;
  } else {
    blocks[0] = 1;
    rfixed[0] = 1;
    if (max_n >= 1) rfixed[1] = 1;
  }

  for (int n = 1; n <= max_n; ++n) {
    if (n >= 3) nonleaf[n] = forests[n - 1] - nonleaf[n - 1];
    if (n >= 2) {
      Count total = 0;
      for (int k = 2; k <= n; ++k) total += nonleaf[k] * blocks[n - k];
      blocks[n] = total;
    }
    if (n >= 3) {
      forests[n] = blocks[n] + 2 * blocks[n - 1] + blocks[n - 2];
    }
    if (n >= 3) {
      centers[n] = rfixed[n - 1] - centers[n - 1];
      Count total = 0;
      for (int a = 0; a <= 1; ++a) {
        for (int left = 0; 2 * a + 2 * left <= n; ++left) {
          int center_size = n - 2 * a - 2 * left;
          if (center_size == 1) continue;
          Count center_count = (center_size == 0) ? 1 : centers[center_size];
          total += blocks[left] * center_count;
        }
      }
      rfixed[n] = total;
    }
  }
}

Word unrank_nonleaf_tree_cpu(int n, Count rank, const Count* nonleaf, const Count* blocks, const Count* forests);
Word unrank_primitive_forest_cpu(int n, Count rank, bool forbid_singleton_nonleaf, const Count* nonleaf, const Count* blocks, const Count* forests);

Word unrank_block_cpu(
    int n,
    Count rank,
    bool require_at_least_two,
    const Count* nonleaf,
    const Count* blocks,
    const Count* forests) {
  if (n == 0) return 0;
  for (int first = 2; first <= n; ++first) {
    if (require_at_least_two && first == n) continue;
    Count class_count = nonleaf[first] * blocks[n - first];
    if (rank < class_count) {
      Count rest_count = blocks[n - first];
      Count tree_rank = rank / rest_count;
      Count rest_rank = rank % rest_count;
      Word t = unrank_nonleaf_tree_cpu(first, tree_rank, nonleaf, blocks, forests);
      Word rest = unrank_block_cpu(n - first, rest_rank, false, nonleaf, blocks, forests);
      return concat_bp(t, first, rest, n - first);
    }
    rank -= class_count;
  }
  throw std::runtime_error("unrank_block_cpu: rank out of range");
}

Word unrank_primitive_forest_cpu(
    int n,
    Count rank,
    bool forbid_singleton_nonleaf,
    const Count* nonleaf,
    const Count* blocks,
    const Count* forests) {
  (void)forests;
  if (n == 0) return 0;
  if (n == 1) return LEAF;
  if (n == 2) {
    if (forbid_singleton_nonleaf) return concat_bp(LEAF, 1, LEAF, 1);
    return (rank == 0) ? concat_bp(LEAF, 1, LEAF, 1) : make_tree(LEAF, 1);
  }

  for (int a = 0; a <= 1; ++a) {
    for (int b = 0; b <= 1; ++b) {
      int core = n - a - b;
      if (core <= 0) continue;
      Count class_count = blocks[core];
      bool require_two = forbid_singleton_nonleaf && a == 0 && b == 0;
      if (require_two) class_count -= nonleaf[core];
      if (class_count == 0) continue;
      if (rank < class_count) {
        Word word = 0;
        int nodes = 0;
        if (a) {
          word = concat_bp(word, nodes, LEAF, 1);
          nodes += 1;
        }
        Word mid = unrank_block_cpu(core, rank, require_two, nonleaf, blocks, forests);
        word = concat_bp(word, nodes, mid, core);
        nodes += core;
        if (b) {
          word = concat_bp(word, nodes, LEAF, 1);
          nodes += 1;
        }
        return word;
      }
      rank -= class_count;
    }
  }
  throw std::runtime_error("unrank_primitive_forest_cpu: rank out of range");
}

Word unrank_nonleaf_tree_cpu(int n, Count rank, const Count* nonleaf, const Count* blocks, const Count* forests) {
  Word child = unrank_primitive_forest_cpu(n - 1, rank, true, nonleaf, blocks, forests);
  return make_tree(child, n - 1);
}

int least_period_dividing_k(Word word, int len, int k) {
  Word cur = word;
  for (int p = 1; p <= k; ++p) {
    cur = M_bp(cur, len);
    if (cur == word) return p;
  }
  return 0;
}

std::vector<Word> orbit_words(Word word, int len, int period) {
  std::vector<Word> out;
  out.reserve(static_cast<size_t>(period));
  Word cur = word;
  for (int i = 0; i < period; ++i) {
    out.push_back(cur);
    cur = M_bp(cur, len);
  }
  return out;
}

template <typename W>
__device__ __forceinline__ int d_bit_at_t(W word, int total_len, int pos) {
  return static_cast<int>((word >> (total_len - 1 - pos)) & static_cast<W>(1));
}

template <typename W, int WordBits>
__device__ __forceinline__ W d_reverse_t(W word) {
  if constexpr (WordBits == 64) {
    return static_cast<W>(__brevll(static_cast<unsigned long long>(word)));
  } else {
    uint64_t lo = static_cast<uint64_t>(word);
    uint64_t hi = static_cast<uint64_t>(word >> 64);
    return (static_cast<W>(d_reverse_t<uint64_t, 64>(lo)) << 64) |
        static_cast<W>(d_reverse_t<uint64_t, 64>(hi));
  }
}

template <typename W, int WordBits>
__device__ __forceinline__ W d_low_mask_t(int len) {
  return (len == WordBits) ? ~static_cast<W>(0) : ((static_cast<W>(1) << len) - 1);
}

template <typename W, int WordBits>
__device__ __forceinline__ W d_revcomp_bp_t(W word, int len) {
  if (len == 0) return 0;
  W rev = d_reverse_t<W, WordBits>(word) >> (WordBits - len);
  return (~rev) & d_low_mask_t<W, WordBits>(len);
}

template <typename W, int MatchStackLen>
__device__ __forceinline__ MatchTable d_build_match_t(W word, int len) {
  MatchTable mt{};
  uint8_t stack[MatchStackLen];
  int top = 0;
  for (int i = 0; i < len; ++i) {
    if (d_bit_at_t(word, len, i)) stack[top++] = static_cast<uint8_t>(i);
    else mt.close[stack[--top]] = static_cast<uint8_t>(i);
  }
  return mt;
}

template <typename W, int MatchStackLen, int FrameStackLen>
__device__ __forceinline__ W d_T_bp_t(W word, int len) {
  MatchTable mt = d_build_match_t<W, MatchStackLen>(word, len);
  W out = 0;
  static constexpr uint16_t close_marker = 0xffff;
  uint16_t stack[FrameStackLen];
  int top = 0;
  stack[top++] = static_cast<uint16_t>(len);
  while (top > 0) {
    uint16_t frame = stack[--top];
    if (frame == close_marker) {
      out <<= 1;
      continue;
    }
    int l = static_cast<int>(frame >> 8);
    int r = static_cast<int>(frame & 0xff);
    if (l >= r) continue;
    int m = mt.close[l];
    out = (out << 1) | static_cast<W>(1);
    stack[top++] = static_cast<uint16_t>(((l + 1) << 8) | m);
    stack[top++] = close_marker;
    stack[top++] = static_cast<uint16_t>(((m + 1) << 8) | r);
  }
  return out;
}

template <typename W, int WordBits, int MatchStackLen, int FrameStackLen>
__device__ __forceinline__ W d_M_bp_t(W word, int len) {
  return d_T_bp_t<W, MatchStackLen, FrameStackLen>(
      d_revcomp_bp_t<W, WordBits>(word, len), len);
}

template <typename W>
__device__ __forceinline__ W d_concat_bp_t(W left, int left_nodes, W right, int right_nodes) {
  (void)left_nodes;
  return (left << (2 * right_nodes)) | right;
}

template <typename W>
__device__ __forceinline__ W d_make_tree_t(W child, int child_nodes) {
  W w = static_cast<W>(1);
  w = (w << (2 * child_nodes)) | child;
  w <<= 1;
  return w;
}

template <typename W>
__device__ W d_unrank_nonleaf_tree_t(int n, Count rank);
template <typename W>
__device__ W d_unrank_primitive_forest_t(int n, Count rank, bool forbid_singleton_nonleaf);

template <typename W>
__device__ W d_unrank_block_t(
    int n,
    Count rank,
    bool require_at_least_two) {
  if (n == 0) return 0;
  int max_first = require_at_least_two ? n - 1 : n;
  if (max_first < 2) return 0;

  for (int first = 2; first <= max_first; ++first) {
    Count class_count = c_nonleaf[first] * c_blocks[n - first];
    if (rank < class_count) {
      Count rest_count = c_blocks[n - first];
      Count tree_rank = rank / rest_count;
      Count rest_rank = rank % rest_count;
      W t = d_unrank_nonleaf_tree_t<W>(first, tree_rank);
      W rest = d_unrank_block_t<W>(n - first, rest_rank, false);
      return d_concat_bp_t(t, first, rest, n - first);
    }
    rank -= class_count;
  }
  return 0;
}

template <typename W>
__device__ W d_unrank_primitive_forest_t(
    int n,
    Count rank,
    bool forbid_singleton_nonleaf) {
  if (n == 0) return 0;
  if (n == 1) return static_cast<W>(LEAF);
  if (n == 2) {
    if (forbid_singleton_nonleaf) return d_concat_bp_t(static_cast<W>(LEAF), 1, static_cast<W>(LEAF), 1);
    return (rank == 0)
        ? d_concat_bp_t(static_cast<W>(LEAF), 1, static_cast<W>(LEAF), 1)
        : d_make_tree_t(static_cast<W>(LEAF), 1);
  }

  for (int a = 0; a <= 1; ++a) {
    for (int b = 0; b <= 1; ++b) {
      int core = n - a - b;
      if (core <= 0) continue;
      Count class_count = c_blocks[core];
      bool require_two = forbid_singleton_nonleaf && a == 0 && b == 0;
      if (require_two) class_count -= c_nonleaf[core];
      if (class_count == 0) continue;
      if (rank < class_count) {
        W word = 0;
        int nodes = 0;
        if (a) {
          word = d_concat_bp_t(word, nodes, static_cast<W>(LEAF), 1);
          nodes += 1;
        }
        W mid = d_unrank_block_t<W>(core, rank, require_two);
        word = d_concat_bp_t(word, nodes, mid, core);
        nodes += core;
        if (b) {
          word = d_concat_bp_t(word, nodes, static_cast<W>(LEAF), 1);
          nodes += 1;
        }
        return word;
      }
      rank -= class_count;
    }
  }
  return 0;
}

template <typename W>
__device__ W d_unrank_nonleaf_tree_t(int n, Count rank) {
  W child = d_unrank_primitive_forest_t<W>(n - 1, rank, true);
  return d_make_tree_t(child, n - 1);
}

template <typename W, int WordBits, int MatchStackLen, int FrameStackLen>
__global__ void primitive_mk_kernel_t(
    int n,
    int k,
    Count total,
    unsigned long long* fixed_points,
    unsigned long long* exact_points,
    unsigned long long* fixed_orbits,
    unsigned long long* exact_orbits,
    Word* orbit_reps,
    unsigned long long orbit_reps_cap) {
  Count gid = static_cast<Count>(blockIdx.x) * static_cast<Count>(blockDim.x) + static_cast<Count>(threadIdx.x);
  Count stride = static_cast<Count>(blockDim.x) * static_cast<Count>(gridDim.x);
  const int len = 2 * n;

  for (Count rank = gid; rank < total; rank += stride) {
    W word = d_unrank_primitive_forest_t<W>(n, rank, false);
    W cur = word;
    W min_word = word;
    bool early_return = false;

    for (int step = 1; step <= k; ++step) {
      cur = d_M_bp_t<W, WordBits, MatchStackLen, FrameStackLen>(cur, len);
      if (cur < min_word) min_word = cur;
      if (step < k && cur == word) early_return = true;
    }

    if (cur != word) continue;

    atomicAdd(fixed_points, 1ull);
    bool canonical = min_word == word;
    if (canonical) {
      unsigned long long idx = atomicAdd(fixed_orbits, 1ull);
      if (orbit_reps && idx < orbit_reps_cap) orbit_reps[idx] = static_cast<Word>(word);
    }
    if (!early_return) {
      atomicAdd(exact_points, 1ull);
      if (canonical) atomicAdd(exact_orbits, 1ull);
    }
  }
}

template <typename T>
void cuda_check(T code, const char* what) {
  if (code != cudaSuccess) throw std::runtime_error(std::string(what) + ": " + cudaGetErrorString(code));
}

Row run_cpu(
    int n,
    int k,
    Count total,
    const std::vector<Count>& nonleaf,
    const std::vector<Count>& blocks,
    const std::vector<Count>& forests,
    int collect_cap) {
  using Clock = std::chrono::steady_clock;

  Row row{};
  if (collect_cap > 0) row.orbit_reps.reserve(static_cast<size_t>(collect_cap));
  const int len = 2 * n;
  auto t0 = Clock::now();
  for (Count rank = 0; rank < total; ++rank) {
    Word word = unrank_primitive_forest_cpu(n, rank, false, nonleaf.data(), blocks.data(), forests.data());
    Word cur = word;
    Word min_word = word;
    bool early_return = false;
    for (int step = 1; step <= k; ++step) {
      cur = M_bp(cur, len);
      if (cur < min_word) min_word = cur;
      if (step < k && cur == word) early_return = true;
    }
    if (cur != word) continue;

    ++row.fixed_points;
    bool canonical = min_word == word;
    if (canonical) {
      ++row.fixed_orbits;
      if (collect_cap > 0 && row.orbit_reps.size() < static_cast<size_t>(collect_cap)) {
        row.orbit_reps.push_back(word);
      }
    }
    if (!early_return) {
      ++row.exact_points;
      if (canonical) ++row.exact_orbits;
    }
  }
  auto t1 = Clock::now();
  row.kernel_ms = static_cast<float>(std::chrono::duration<double, std::milli>(t1 - t0).count());
  return row;
}

Row run_gpu(
    int n,
    int k,
    Count total,
    const std::vector<Count>& nonleaf,
    const std::vector<Count>& blocks,
    const std::vector<Count>& forests,
    int threads,
    int collect_cap) {
  Row row{};

  unsigned long long* fixed_points_d = nullptr;
  unsigned long long* exact_points_d = nullptr;
  unsigned long long* fixed_orbits_d = nullptr;
  unsigned long long* exact_orbits_d = nullptr;
  Word* orbit_reps_d = nullptr;

  size_t count_bytes = nonleaf.size() * sizeof(Count);
  cuda_check(cudaMemcpyToSymbol(c_nonleaf, nonleaf.data(), count_bytes), "memcpy constant nonleaf");
  cuda_check(cudaMemcpyToSymbol(c_blocks, blocks.data(), count_bytes), "memcpy constant blocks");
  cuda_check(cudaMalloc(&fixed_points_d, sizeof(unsigned long long)), "cudaMalloc fixed points");
  cuda_check(cudaMalloc(&exact_points_d, sizeof(unsigned long long)), "cudaMalloc exact points");
  cuda_check(cudaMalloc(&fixed_orbits_d, sizeof(unsigned long long)), "cudaMalloc fixed orbits");
  cuda_check(cudaMalloc(&exact_orbits_d, sizeof(unsigned long long)), "cudaMalloc exact orbits");
  if (collect_cap > 0) {
    cuda_check(cudaMalloc(&orbit_reps_d, static_cast<size_t>(collect_cap) * sizeof(Word)), "cudaMalloc orbit reps");
  }

  cuda_check(cudaMemset(fixed_points_d, 0, sizeof(unsigned long long)), "memset fixed points");
  cuda_check(cudaMemset(exact_points_d, 0, sizeof(unsigned long long)), "memset exact points");
  cuda_check(cudaMemset(fixed_orbits_d, 0, sizeof(unsigned long long)), "memset fixed orbits");
  cuda_check(cudaMemset(exact_orbits_d, 0, sizeof(unsigned long long)), "memset exact orbits");
  cuda_check(cudaDeviceSetLimit(cudaLimitStackSize, 32768), "cudaDeviceSetLimit stack");

  cudaDeviceProp prop{};
  cuda_check(cudaGetDeviceProperties(&prop, 0), "cudaGetDeviceProperties");
  Count requested_blocks = (total + static_cast<Count>(threads) - 1) / static_cast<Count>(threads);
  int grid_cap = prop.maxGridSize[0] > 0 ? prop.maxGridSize[0] : 65535;
  int launch_blocks = static_cast<int>(std::min<Count>(std::max<Count>(requested_blocks, 1), static_cast<Count>(grid_cap)));

  cudaEvent_t ev_start;
  cudaEvent_t ev_stop;
  cuda_check(cudaEventCreate(&ev_start), "event create start");
  cuda_check(cudaEventCreate(&ev_stop), "event create stop");
  cuda_check(cudaEventRecord(ev_start), "event record start");
  if (n <= 16) {
    primitive_mk_kernel_t<uint64_t, 64, 16, 33><<<launch_blocks, threads>>>(
        n,
        k,
        total,
        fixed_points_d,
        exact_points_d,
        fixed_orbits_d,
        exact_orbits_d,
        orbit_reps_d,
        static_cast<unsigned long long>(collect_cap));
  } else if (n <= 24) {
    primitive_mk_kernel_t<uint64_t, 64, 24, 49><<<launch_blocks, threads>>>(
        n,
        k,
        total,
        fixed_points_d,
        exact_points_d,
        fixed_orbits_d,
        exact_orbits_d,
        orbit_reps_d,
        static_cast<unsigned long long>(collect_cap));
  } else if (n <= 32) {
    primitive_mk_kernel_t<uint64_t, 64, 32, 65><<<launch_blocks, threads>>>(
        n,
        k,
        total,
        fixed_points_d,
        exact_points_d,
        fixed_orbits_d,
        exact_orbits_d,
        orbit_reps_d,
        static_cast<unsigned long long>(collect_cap));
  } else {
    primitive_mk_kernel_t<Word, 128, 64, 2 * MAX_N + 1><<<launch_blocks, threads>>>(
        n,
        k,
        total,
        fixed_points_d,
        exact_points_d,
        fixed_orbits_d,
        exact_orbits_d,
        orbit_reps_d,
        static_cast<unsigned long long>(collect_cap));
  }
  cuda_check(cudaGetLastError(), "kernel launch");
  cuda_check(cudaDeviceSynchronize(), "kernel sync");
  cuda_check(cudaEventRecord(ev_stop), "event record stop");
  cuda_check(cudaEventSynchronize(ev_stop), "event sync stop");
  cuda_check(cudaEventElapsedTime(&row.kernel_ms, ev_start, ev_stop), "elapsed kernel");

  cuda_check(cudaMemcpy(&row.fixed_points, fixed_points_d, sizeof(unsigned long long), cudaMemcpyDeviceToHost), "memcpy fixed points");
  cuda_check(cudaMemcpy(&row.exact_points, exact_points_d, sizeof(unsigned long long), cudaMemcpyDeviceToHost), "memcpy exact points");
  cuda_check(cudaMemcpy(&row.fixed_orbits, fixed_orbits_d, sizeof(unsigned long long), cudaMemcpyDeviceToHost), "memcpy fixed orbits");
  cuda_check(cudaMemcpy(&row.exact_orbits, exact_orbits_d, sizeof(unsigned long long), cudaMemcpyDeviceToHost), "memcpy exact orbits");

  if (collect_cap > 0 && row.fixed_orbits > 0) {
    unsigned long long take = std::min<unsigned long long>(row.fixed_orbits, static_cast<unsigned long long>(collect_cap));
    row.orbit_reps.resize(static_cast<size_t>(take));
    cuda_check(cudaMemcpy(row.orbit_reps.data(), orbit_reps_d, static_cast<size_t>(take) * sizeof(Word), cudaMemcpyDeviceToHost), "memcpy orbit reps");
    std::sort(row.orbit_reps.begin(), row.orbit_reps.end());
    row.orbit_reps.erase(std::unique(row.orbit_reps.begin(), row.orbit_reps.end()), row.orbit_reps.end());
  }

  cudaEventDestroy(ev_start);
  cudaEventDestroy(ev_stop);
  cudaFree(fixed_points_d);
  cudaFree(exact_points_d);
  cudaFree(fixed_orbits_d);
  cudaFree(exact_orbits_d);
  if (orbit_reps_d) cudaFree(orbit_reps_d);
  return row;
}

bool parity_forces_zero(int n, int k) {
  return n > 0 && (n % 2 == 0) && (k % 2 == 1);
}

void print_usage(const char* exe) {
  std::cerr
      << "usage: " << exe << " --k K [--n N | --from A --to B | --max-n N]\n"
      << "       [--threads T] [--cpu] [--print-orbits] [--collect-cap C]\n";
}

}  // namespace

int main(int argc, char** argv) {
  int k = 2;
  int from = 14;
  int to = 14;
  int threads = 512;
  int collect_cap = 0;
  bool use_cpu = false;
  bool print_orbits = false;

  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&](int& x) {
      if (i + 1 >= argc) throw std::runtime_error("missing value for " + a);
      x = std::stoi(argv[++i]);
    };
    if (a == "--k") next(k);
    else if (a == "--n") {
      next(from);
      to = from;
    } else if (a == "--from") next(from);
    else if (a == "--to") next(to);
    else if (a == "--max-n") {
      from = 0;
      next(to);
    } else if (a == "--threads") next(threads);
    else if (a == "--collect-cap") next(collect_cap);
    else if (a == "--cpu") use_cpu = true;
    else if (a == "--print-orbits") print_orbits = true;
    else {
      print_usage(argv[0]);
      std::cerr << "unknown flag: " << a << "\n";
      return 1;
    }
  }
  if (print_orbits && collect_cap == 0) collect_cap = 4096;

  if (k <= 0) {
    std::cerr << "k must be positive\n";
    return 1;
  }
  if (from < 0 || to < from || to > MAX_N) {
    std::cerr << "Require 0 <= from <= to <= " << MAX_N << "\n";
    return 1;
  }
  if (threads <= 0) {
    std::cerr << "threads must be positive\n";
    return 1;
  }

  std::vector<Count> nonleaf;
  std::vector<Count> blocks;
  std::vector<Count> forests;
  std::vector<Count> centers;
  std::vector<Count> rfixed;
  build_counts(to, nonleaf, blocks, forests, centers, rfixed);

  bool needs_search = false;
  for (int n = from; n <= to; ++n) {
    if (!parity_forces_zero(n, k)) {
      needs_search = true;
      break;
    }
  }

  bool have_gpu = false;
  if (needs_search) {
    int device_count = 0;
    cudaError_t dev_err = cudaGetDeviceCount(&device_count);
    have_gpu = dev_err == cudaSuccess && device_count > 0;
    if (!have_gpu) use_cpu = true;
    if (have_gpu) cuda_check(cudaSetDevice(0), "cudaSetDevice");
  }

  std::cout << "n k backend primitive fixed_points fixed_orbits exact_points exact_orbits kernel_ms\n";
  for (int n = from; n <= to; ++n) {
    Count total = forests[n];
    bool parity_skip = parity_forces_zero(n, k);
    Row row{};
    if (!parity_skip) {
      row = use_cpu
          ? run_cpu(n, k, total, nonleaf, blocks, forests, collect_cap)
          : run_gpu(n, k, total, nonleaf, blocks, forests, threads, collect_cap);
    }

    std::cout << n << " " << k << " " << (parity_skip ? "parity" : (use_cpu ? "cpu" : "gpu")) << " "
              << total << " " << row.fixed_points << " " << row.fixed_orbits << " "
              << row.exact_points << " " << row.exact_orbits << " "
              << row.kernel_ms << "\n";

    if (print_orbits && row.fixed_orbits > 0) {
      if (row.fixed_orbits > static_cast<unsigned long long>(collect_cap)) {
        std::cout << "orbit_words_truncated " << row.orbit_reps.size()
                  << " of " << row.fixed_orbits << "\n";
      }
      std::cout << "orbit_index period orbit_words\n";
      int orbit_idx = 0;
      for (Word rep : row.orbit_reps) {
        int period = least_period_dividing_k(rep, 2 * n, k);
        std::vector<Word> words = orbit_words(rep, 2 * n, period);
        ++orbit_idx;
        std::cout << orbit_idx << " " << period << " ";
        for (size_t i = 0; i < words.size(); ++i) {
          if (i > 0) std::cout << " | ";
          std::cout << to_string_bp(words[i], 2 * n);
        }
        std::cout << "\n";
      }
    }
  }

  return 0;
}
