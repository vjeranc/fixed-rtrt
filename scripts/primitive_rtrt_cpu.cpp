#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

namespace {

using Word = unsigned __int128;
using Count = uint64_t;

static constexpr int MAX_N = 64;
static constexpr Word LEAF = static_cast<Word>(2);

struct MatchTable {
  uint8_t close[128];
};

struct WordHash {
  size_t operator()(Word w) const {
    uint64_t lo = static_cast<uint64_t>(w);
    uint64_t hi = static_cast<uint64_t>(w >> 64);
    return static_cast<size_t>(lo ^ (hi * 0x9E3779B97F4A7C15ULL));
  }
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
  Word rev = reverse128(word) >> (128 - len);
  return (~rev) & low_mask(len);
}

std::string to_string_bp(Word word, int total_len) {
  std::string out;
  out.reserve(total_len);
  for (int i = 0; i < total_len; ++i) out.push_back(bit_at(word, total_len, i) ? '(' : ')');
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

Word unrank_nonleaf_tree_cpu(int n, Count rank, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed);
Word unrank_primitive_forest_cpu(int n, Count rank, bool forbid_singleton_nonleaf, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed);
Word unrank_rfixed_forest_cpu(int n, Count rank, bool forbid_singleton_nonleaf, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed);

Word unrank_block_cpu(int n, Count rank, bool require_at_least_two, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed) {
  if (n == 0) return 0;
  for (int first = 2; first <= n; ++first) {
    if (require_at_least_two && first == n) continue;
    Count class_count = nonleaf[first] * blocks[n - first];
    if (rank < class_count) {
      Count rest_count = blocks[n - first];
      Count tree_rank = rank / rest_count;
      Count rest_rank = rank % rest_count;
      Word t = unrank_nonleaf_tree_cpu(first, tree_rank, nonleaf, blocks, forests, centers, rfixed);
      Word rest = unrank_block_cpu(n - first, rest_rank, false, nonleaf, blocks, forests, centers, rfixed);
      return concat_bp(t, first, rest, n - first);
    }
    rank -= class_count;
  }
  throw std::runtime_error("unrank_block_cpu: rank out of range");
}

Word unrank_primitive_forest_cpu(int n, Count rank, bool forbid_singleton_nonleaf, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed) {
  (void)centers;
  (void)rfixed;
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
        Word mid = unrank_block_cpu(core, rank, require_two, nonleaf, blocks, forests, centers, rfixed);
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

Word unrank_nonleaf_tree_cpu(int n, Count rank, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed) {
  Word child = unrank_primitive_forest_cpu(n - 1, rank, true, nonleaf, blocks, forests, centers, rfixed);
  return make_tree(child, n - 1);
}

Word unrank_center_tree_cpu(int n, Count rank, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed) {
  Word child = unrank_rfixed_forest_cpu(n - 1, rank, true, nonleaf, blocks, forests, centers, rfixed);
  return make_tree(child, n - 1);
}

Word unrank_rfixed_forest_cpu(int n, Count rank, bool forbid_singleton_nonleaf, const Count* nonleaf, const Count* blocks, const Count* forests, const Count* centers, const Count* rfixed) {
  (void)forests;
  if (n == 0) return 0;
  if (n == 1) return LEAF;

  for (int a = 0; a <= 1; ++a) {
    for (int left = 0; 2 * a + 2 * left <= n; ++left) {
      int center_size = n - 2 * a - 2 * left;
      if (center_size == 1) continue;
      if (forbid_singleton_nonleaf && a == 0 && left == 0 && center_size >= 2) continue;

      Count center_count = (center_size == 0) ? 1 : centers[center_size];
      Count class_count = blocks[left] * center_count;
      if (rank < class_count) {
        Count left_rank = rank % blocks[left];
        Count center_rank = rank / blocks[left];

        Word left_word = unrank_block_cpu(left, left_rank, false, nonleaf, blocks, forests, centers, rfixed);
        Word center_word = 0;
        if (center_size >= 2) center_word = unrank_center_tree_cpu(center_size, center_rank, nonleaf, blocks, forests, centers, rfixed);
        Word right_word = revcomp_bp(left_word, 2 * left);

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
      rank -= class_count;
    }
  }
  throw std::runtime_error("unrank_rfixed_forest_cpu: rank out of range");
}

void print_header() {
  std::cout << "n backend domain fixed kernel_ms\n";
}

void print_row(int n, const char* backend, Count domain, unsigned long long fixed, double kernel_ms) {
  std::cout << n << " " << backend << " " << domain << " " << fixed << " " << kernel_ms << "\n";
}

void print_orbit_header() {
  std::cout << "orbit_index orbit_words\n";
}

unsigned long long count_fixed_only(
    int n,
    Count domain,
    const Count* nonleaf,
    const Count* blocks,
    const Count* forests,
    const Count* centers,
    const Count* rfixed) {
  const int len = 2 * n;
  unsigned long long fixed = 0;

#ifdef _OPENMP
#pragma omp parallel for schedule(guided, 256) reduction(+:fixed)
  for (Count rank = 0; rank < domain; ++rank) {
    Word word = unrank_rfixed_forest_cpu(n, rank, false, nonleaf, blocks, forests, centers, rfixed);
    Word tf = T_bp(word, len);
    fixed += static_cast<unsigned long long>(revcomp_bp(tf, len) == tf);
  }
#else
  for (Count rank = 0; rank < domain; ++rank) {
    Word word = unrank_rfixed_forest_cpu(n, rank, false, nonleaf, blocks, forests, centers, rfixed);
    Word tf = T_bp(word, len);
    fixed += static_cast<unsigned long long>(revcomp_bp(tf, len) == tf);
  }
#endif

  return fixed;
}

}  // namespace

int main(int argc, char** argv) {
  using Clock = std::chrono::steady_clock;

  int n = 17;
  int threads = 1;
  int collect_cap = 0;
  bool print_orbits = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&](int& x) { x = std::stoi(argv[++i]); };
    if (a == "--n" && i + 1 < argc) next(n);
    else if (a == "--threads" && i + 1 < argc) next(threads);
    else if (a == "--collect-cap" && i + 1 < argc) next(collect_cap);
    else if (a == "--print-orbits") print_orbits = true;
    else {
      std::cerr << "unknown flag: " << a << "\n";
      return 1;
    }
  }
  if (print_orbits && collect_cap == 0) collect_cap = 4096;

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

  std::vector<Count> nonleaf_h, blocks_h, forests_h, centers_h, rfixed_h;
  build_counts(n, nonleaf_h, blocks_h, forests_h, centers_h, rfixed_h);
  Count domain = rfixed_h[n];

  auto t0 = Clock::now();
  unsigned long long fixed = 0;
  std::vector<Word> fixed_words;
  if (collect_cap == 0) {
    fixed = count_fixed_only(
        n, domain,
        nonleaf_h.data(), blocks_h.data(), forests_h.data(), centers_h.data(), rfixed_h.data());
  } else {
    fixed_words.reserve(static_cast<size_t>(collect_cap));
#ifdef _OPENMP
#pragma omp parallel
    {
      unsigned long long local_fixed = 0;
      std::vector<Word> local_words;
      local_words.reserve(std::min<int>(collect_cap, 1024));

#pragma omp for schedule(dynamic, 256)
      for (Count rank = 0; rank < domain; ++rank) {
        Word word = unrank_rfixed_forest_cpu(n, rank, false, nonleaf_h.data(), blocks_h.data(), forests_h.data(), centers_h.data(), rfixed_h.data());
        Word tf = T_bp(word, 2 * n);
        if (revcomp_bp(tf, 2 * n) == tf) {
          ++local_fixed;
          if (local_words.size() < static_cast<size_t>(collect_cap)) local_words.push_back(word);
        }
      }

#pragma omp atomic
      fixed += local_fixed;

      if (!local_words.empty()) {
#pragma omp critical
        {
          size_t room = fixed_words.size() < static_cast<size_t>(collect_cap)
              ? static_cast<size_t>(collect_cap) - fixed_words.size()
              : 0;
          size_t take = std::min(room, local_words.size());
          fixed_words.insert(fixed_words.end(), local_words.begin(), local_words.begin() + static_cast<long>(take));
        }
      }
    }
#else
    for (Count rank = 0; rank < domain; ++rank) {
      Word word = unrank_rfixed_forest_cpu(n, rank, false, nonleaf_h.data(), blocks_h.data(), forests_h.data(), centers_h.data(), rfixed_h.data());
      Word tf = T_bp(word, 2 * n);
      if (revcomp_bp(tf, 2 * n) == tf) {
        ++fixed;
        if (fixed_words.size() < static_cast<size_t>(collect_cap)) fixed_words.push_back(word);
      }
    }
#endif
  }
  auto t1 = Clock::now();
  double kernel_ms = std::chrono::duration<double, std::milli>(t1 - t0).count();

  print_header();
  print_row(n, "cpu", domain, fixed, kernel_ms);

  if (print_orbits && collect_cap > 0 && fixed > 0 && fixed <= static_cast<unsigned long long>(collect_cap)) {
    print_orbit_header();
    std::sort(fixed_words.begin(), fixed_words.end());
    fixed_words.erase(std::unique(fixed_words.begin(), fixed_words.end()), fixed_words.end());
    std::unordered_set<Word, WordHash> seen;
    int orbit_idx = 0;
    for (Word f : fixed_words) {
      if (seen.count(f)) continue;
      Word tf = T_bp(f, 2 * n);
      ++orbit_idx;
      std::cout << orbit_idx << " " << to_string_bp(f, 2 * n) << " | " << to_string_bp(tf, 2 * n) << "\n";
      seen.insert(f);
      seen.insert(tf);
    }
  }

  return 0;
}
