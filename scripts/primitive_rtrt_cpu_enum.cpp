#include <algorithm>
#include <chrono>
#include <cstdint>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

namespace {

using Word = unsigned __int128;
using Count = uint64_t;

static constexpr int MAX_N = 64;
static constexpr Word LEAF = static_cast<Word>(2);

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
  Word rev = reverse128(word) >> (128 - len);
  return (~rev) & low_mask(len);
}

int first_tree_end(Word word, int total_len) {
  int balance = 0;
  for (int i = 0; i < total_len; ++i) {
    balance += bit_at(word, total_len, i) ? 1 : -1;
    if (balance == 0) return i;
  }
  return -1;
}

bool is_singleton_tree_forest(Word word, int node_count) {
  if (node_count <= 0) return false;
  return first_tree_end(word, 2 * node_count) == 2 * node_count - 1;
}

struct MatchTable {
  uint8_t close[128];
};

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
    if (n >= 3) forests[n] = blocks[n] + 2 * blocks[n - 1] + blocks[n - 2];
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

struct Job {
  int a;
  int left_size;
  int center_size;
  Count domain;
};

struct Enumerator {
  int n;
  int block_cache_max;
  int nonleaf_cache_max;
  int rfixed_cache_max;
  const std::vector<Count>& nonleaf_counts;
  const std::vector<Count>& block_counts;
  const std::vector<Count>& forest_counts;
  const std::vector<Count>& center_counts;
  const std::vector<Count>& rfixed_counts;

  std::vector<std::vector<Word>> block_cache;
  std::vector<std::vector<Word>> nonleaf_cache;
  std::vector<std::vector<Word>> rfixed_cache;
  std::vector<char> block_done;
  std::vector<char> nonleaf_done;
  std::vector<char> rfixed_done;

  Enumerator(
      int n_,
      int block_cache_max_,
      int nonleaf_cache_max_,
      int rfixed_cache_max_,
      const std::vector<Count>& nonleaf_counts_,
      const std::vector<Count>& block_counts_,
      const std::vector<Count>& forest_counts_,
      const std::vector<Count>& center_counts_,
      const std::vector<Count>& rfixed_counts_)
      : n(n_),
        block_cache_max(std::min(n_, block_cache_max_)),
        nonleaf_cache_max(std::min(n_, nonleaf_cache_max_)),
        rfixed_cache_max(std::min(n_, rfixed_cache_max_)),
        nonleaf_counts(nonleaf_counts_),
        block_counts(block_counts_),
        forest_counts(forest_counts_),
        center_counts(center_counts_),
        rfixed_counts(rfixed_counts_),
        block_cache(n_ + 1),
        nonleaf_cache(n_ + 1),
        rfixed_cache(n_ + 1),
        block_done(n_ + 1, 0),
        nonleaf_done(n_ + 1, 0),
        rfixed_done(n_ + 1, 0) {}

  void warm_caches() {
    for (int s = 0; s <= block_cache_max; ++s) ensure_block_cache(s);
    for (int s = 0; s <= nonleaf_cache_max; ++s) ensure_nonleaf_cache(s);
    for (int s = 0; s <= rfixed_cache_max; ++s) ensure_rfixed_cache(s);
  }

  void ensure_block_cache(int s) {
    if (s > block_cache_max || block_done[s]) return;
    auto& out = block_cache[s];
    out.reserve(static_cast<size_t>(block_counts[s]));
    for_each_block_uncached(s, false, [&](Word w) { out.push_back(w); });
    block_done[s] = 1;
  }

  void ensure_nonleaf_cache(int s) {
    if (s > nonleaf_cache_max || nonleaf_done[s]) return;
    auto& out = nonleaf_cache[s];
    out.reserve(static_cast<size_t>(nonleaf_counts[s]));
    for_each_nonleaf_tree_uncached(s, [&](Word w) { out.push_back(w); });
    nonleaf_done[s] = 1;
  }

  void ensure_rfixed_cache(int s) {
    if (s > rfixed_cache_max || rfixed_done[s]) return;
    auto& out = rfixed_cache[s];
    out.reserve(static_cast<size_t>(rfixed_counts[s]));
    for_each_rfixed_uncached(s, false, [&](Word w) { out.push_back(w); });
    rfixed_done[s] = 1;
  }

  void for_each_block(int s, bool require_two, const std::function<void(Word)>& emit) {
    if (s <= block_cache_max) {
      ensure_block_cache(s);
      for (Word w : block_cache[s]) {
        if (require_two && is_singleton_tree_forest(w, s) && w != LEAF) continue;
        emit(w);
      }
      return;
    }
    for_each_block_uncached(s, require_two, emit);
  }

  void for_each_nonleaf_tree(int s, const std::function<void(Word)>& emit) {
    if (s <= nonleaf_cache_max) {
      ensure_nonleaf_cache(s);
      for (Word w : nonleaf_cache[s]) emit(w);
      return;
    }
    for_each_nonleaf_tree_uncached(s, emit);
  }

  void for_each_rfixed(int s, bool forbid_singleton_nonleaf, const std::function<void(Word)>& emit) {
    if (s <= rfixed_cache_max) {
      ensure_rfixed_cache(s);
      for (Word w : rfixed_cache[s]) {
        if (forbid_singleton_nonleaf && is_singleton_tree_forest(w, s) && w != LEAF) continue;
        emit(w);
      }
      return;
    }
    for_each_rfixed_uncached(s, forbid_singleton_nonleaf, emit);
  }

  void for_each_nonleaf_tree_uncached(int s, const std::function<void(Word)>& emit) {
    if (s <= 1) return;
    for_each_primitive_forest(s - 1, true, [&](Word child) {
      emit(make_tree(child, s - 1));
    });
  }

  void for_each_primitive_forest(int s, bool forbid_singleton_nonleaf, const std::function<void(Word)>& emit) {
    if (s == 0) {
      emit(static_cast<Word>(0));
      return;
    }
    if (s == 1) {
      emit(LEAF);
      return;
    }
    for (int a = 0; a <= 1; ++a) {
      for (int b = 0; b <= 1; ++b) {
        int core = s - a - b;
        if (core <= 0) continue;
        bool require_two = forbid_singleton_nonleaf && a == 0 && b == 0;
        for_each_block(core, require_two, [&](Word mid) {
          Word word = 0;
          int nodes = 0;
          if (a) {
            word = concat_bp(word, nodes, LEAF, 1);
            nodes += 1;
          }
          word = concat_bp(word, nodes, mid, core);
          nodes += core;
          if (b) {
            word = concat_bp(word, nodes, LEAF, 1);
            nodes += 1;
          }
          emit(word);
        });
      }
    }
  }

  void for_each_block_uncached(int s, bool require_two, const std::function<void(Word)>& emit) {
    if (s == 0) {
      emit(static_cast<Word>(0));
      return;
    }
    for (int first = 2; first <= s; ++first) {
      if (require_two && first == s) continue;
      for_each_nonleaf_tree(first, [&](Word t) {
        for_each_block(s - first, false, [&](Word rest) {
          emit(concat_bp(t, first, rest, s - first));
        });
      });
    }
  }

  void for_each_rfixed_uncached(int s, bool forbid_singleton_nonleaf, const std::function<void(Word)>& emit) {
    if (s == 0) {
      emit(static_cast<Word>(0));
      return;
    }
    if (s == 1) {
      emit(LEAF);
      return;
    }
    for (int a = 0; a <= 1; ++a) {
      for (int left = 0; 2 * a + 2 * left <= s; ++left) {
        int center_size = s - 2 * a - 2 * left;
        if (center_size == 1) continue;
        if (forbid_singleton_nonleaf && a == 0 && left == 0 && center_size >= 2) continue;
        for_each_block(left, false, [&](Word left_word) {
          Word right_word = revcomp_bp(left_word, 2 * left);
          if (center_size == 0) {
            emit(build_rfixed_word(a, left, left_word, center_size, 0, right_word));
          } else {
            for_each_rfixed(center_size - 1, true, [&](Word child) {
              Word center_word = make_tree(child, center_size - 1);
              emit(build_rfixed_word(a, left, left_word, center_size, center_word, right_word));
            });
          }
        });
      }
    }
  }

  static Word build_rfixed_word(int a, int left, Word left_word, int center_size, Word center_word, Word right_word) {
    Word word = 0;
    int nodes = 0;
    if (a) {
      word = concat_bp(word, nodes, LEAF, 1);
      nodes += 1;
    }
    word = concat_bp(word, nodes, left_word, left);
    nodes += left;
    if (center_size >= 2) {
      word = concat_bp(word, nodes, center_word, center_size);
      nodes += center_size;
    }
    word = concat_bp(word, nodes, right_word, left);
    nodes += left;
    if (a) {
      word = concat_bp(word, nodes, LEAF, 1);
      nodes += 1;
    }
    return word;
  }

  uint64_t count_job(const Job& job) {
    const int len = 2 * n;
    uint64_t fixed = 0;
    for_each_block(job.left_size, false, [&](Word left_word) {
      Word right_word = revcomp_bp(left_word, 2 * job.left_size);
      if (job.center_size == 0) {
        Word word = build_rfixed_word(job.a, job.left_size, left_word, 0, 0, right_word);
        Word tf = T_bp(word, len);
        fixed += static_cast<uint64_t>(revcomp_bp(tf, len) == tf);
      } else {
        for_each_rfixed(job.center_size - 1, true, [&](Word child) {
          Word center_word = make_tree(child, job.center_size - 1);
          Word word = build_rfixed_word(job.a, job.left_size, left_word, job.center_size, center_word, right_word);
          Word tf = T_bp(word, len);
          fixed += static_cast<uint64_t>(revcomp_bp(tf, len) == tf);
        });
      }
    });
    return fixed;
  }
};

std::vector<Job> build_jobs(int n, const std::vector<Count>& blocks, const std::vector<Count>& centers) {
  std::vector<Job> jobs;
  if (n == 0) {
    jobs.push_back({0, 0, 0, 1});
    return jobs;
  }
  if (n == 1) {
    jobs.push_back({0, 0, 1, 1});
    return jobs;
  }
  for (int a = 0; a <= 1; ++a) {
    for (int left = 0; 2 * a + 2 * left <= n; ++left) {
      int center_size = n - 2 * a - 2 * left;
      if (center_size == 1) continue;
      Count center_count = (center_size == 0) ? 1 : centers[center_size];
      jobs.push_back({a, left, center_size, blocks[left] * center_count});
    }
  }
  std::sort(jobs.begin(), jobs.end(), [](const Job& x, const Job& y) {
    return x.domain > y.domain;
  });
  return jobs;
}

}  // namespace

int main(int argc, char** argv) {
  using Clock = std::chrono::steady_clock;

  int n = 42;
  int threads = 12;
  int block_cache_max = 18;
  int nonleaf_cache_max = 18;
  int rfixed_cache_max = 30;

  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&](int& x) { x = std::stoi(argv[++i]); };
    if (a == "--n" && i + 1 < argc) next(n);
    else if (a == "--threads" && i + 1 < argc) next(threads);
    else if (a == "--block-cache-max" && i + 1 < argc) next(block_cache_max);
    else if (a == "--nonleaf-cache-max" && i + 1 < argc) next(nonleaf_cache_max);
    else if (a == "--rfixed-cache-max" && i + 1 < argc) next(rfixed_cache_max);
    else {
      std::cerr << "unknown flag: " << a << "\n";
      return 1;
    }
  }

  if (n < 0 || n > MAX_N) {
    std::cerr << "Require 0 <= n <= 64\n";
    return 1;
  }
  if (threads <= 0) {
    std::cerr << "threads must be positive\n";
    return 1;
  }

#ifdef _OPENMP
  omp_set_num_threads(threads);
#else
  (void)threads;
#endif

  std::vector<Count> nonleaf, blocks, forests, centers, rfixed;
  build_counts(n, nonleaf, blocks, forests, centers, rfixed);
  Count domain = rfixed[n];

  auto t0 = Clock::now();
  Enumerator enumerator(n, block_cache_max, nonleaf_cache_max, rfixed_cache_max, nonleaf, blocks, forests, centers, rfixed);
  enumerator.warm_caches();
  auto t1 = Clock::now();

  std::vector<Job> jobs = build_jobs(n, blocks, centers);
  uint64_t fixed = 0;

#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 1) reduction(+:fixed)
  for (int i = 0; i < static_cast<int>(jobs.size()); ++i) {
    fixed += enumerator.count_job(jobs[i]);
  }
#else
  for (const Job& job : jobs) fixed += enumerator.count_job(job);
#endif

  auto t2 = Clock::now();
  double init_ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
  double kernel_ms = std::chrono::duration<double, std::milli>(t2 - t1).count();
  double total_ms = std::chrono::duration<double, std::milli>(t2 - t0).count();

  std::cout << "n backend domain fixed init_ms kernel_ms total_ms\n";
  std::cout << n << " cpu-enum " << domain << " " << fixed << " "
            << init_ms << " " << kernel_ms << " " << total_ms << "\n";
  return 0;
}
