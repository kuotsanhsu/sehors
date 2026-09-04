// make CXXFLAGS='-std=c++23 -g -DDEBUG' cycle_detection && ./cycle_detection
// make CXXFLAGS='-std=c++23 -O2' cycle_detection &&
// 	for i in {1..3}; do ./cycle_detection < sample$i.txt; done
#pragma GCC optimize "Ofast"

#ifndef	DEBUG
#define	NDEBUG
#endif
// #define	NDEBUG

#include <array>
#include <bit>
#include <algorithm>
#include <cassert>
#include <utility>
#include <string_view>
#include <span>
#include <cstdint>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>

constexpr auto operator""_Ki(unsigned long long nbyte) noexcept {return nbyte << 10;}
constexpr auto operator""_Mi(unsigned long long nbyte) noexcept {return nbyte << 20;}

#ifdef	ONLINE_JUDGE
// AMD EPYC 7B13 is proprietary OEM for GCP which is closest to
// https://www.amd.com/en/products/processors/server/epyc/7003-series/amd-epyc-7713.html
// https://www.reddit.com/r/LocalLLaMA/comments/1mjv9r8/comment/n7dz3y8/
constexpr std::size_t level1_icache_size	= 32_Ki;	// _SC_LEVEL1_ICACHE_SIZE
constexpr std::size_t level1_icache_assoc	= 8;		// _SC_LEVEL1_ICACHE_ASSOC
constexpr std::size_t level1_icache_linesize	= 64;		// _SC_LEVEL1_ICACHE_LINESIZE
constexpr std::size_t level1_dcache_size	= 32_Ki;	// _SC_LEVEL1_DCACHE_SIZE
constexpr std::size_t level1_dcache_assoc	= 8;		// _SC_LEVEL1_DCACHE_ASSOC
constexpr std::size_t level1_dcache_linesize	= 64;		// _SC_LEVEL1_DCACHE_LINESIZE
constexpr std::size_t level2_cache_size		= 512_Ki;	// _SC_LEVEL2_CACHE_SIZE
constexpr std::size_t level2_cache_assoc	= 8;		// _SC_LEVEL2_CACHE_ASSOC
constexpr std::size_t level2_cache_linesize	= 64;		// _SC_LEVEL2_CACHE_LINESIZE
constexpr std::size_t level3_cache_size		= 32_Mi;	// _SC_LEVEL3_CACHE_SIZE
constexpr std::size_t level3_cache_assoc	= 16;		// _SC_LEVEL3_CACHE_ASSOC
constexpr std::size_t level3_cache_linesize	= 64;		// _SC_LEVEL3_CACHE_LINESIZE
#endif

[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] constexpr std::string_view
read_file(const int fd) noexcept {
	struct ::stat stat;
	if (::fstat(fd, &stat) == -1) [[unlikely]] return {};
	const std::size_t input_size = stat.st_size;
	if (input_size == 0) [[unlikely]] return {};
#ifndef	MAP_POPULATE
#define	MAP_POPULATE MAP_FILE
#endif
	const auto input = ::mmap(nullptr, input_size, PROT_READ, MAP_PRIVATE | MAP_POPULATE, fd, 0);
	if (input == MAP_FAILED) [[unlikely]] return {};
	return {static_cast<const char*>(input), input_size};
}

[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] constexpr int
parse_int(const char *&c, const char *const last, const char delimiter) noexcept {
	int integer = 0;
	assert(c != last);
	do {
		assert('0' <= *c and *c <= '9');
		integer *= 10;
		integer += *c - '0';
		++c;
		assert(c != last);
	} while (*c != delimiter);
	++c;
	return integer;
}

[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] constexpr std::uint64_t
swar2(unsigned n) noexcept {
	constexpr std::array<unsigned short, 100> table = [] constexpr noexcept {
		constexpr std::string_view digits = "0123456789";
		static_assert(digits.size() == 10);
		std::array<unsigned short, 100> table;
		auto swar = table.begin();
		for (const auto tens : digits) {
			const auto tens_swar = tens << __CHAR_BIT__ * 0;
			for (const auto ones : digits) {
				const auto ones_swar = ones << __CHAR_BIT__ * 1;
				*swar++ = ones_swar ^ tens_swar;
			} 
		}
		assert(swar == table.end());
		return table;
	}();
	constexpr char initial[8] = "\n      ";
	auto swar = std::bit_cast<std::uint64_t>(initial);
	do {
		swar <<= __CHAR_BIT__ * 2;
		swar ^= table[n % 100];
		n /= 100;
	} while (n != 0);
	if ((swar & 0xf) == 0) swar ^= '0' ^ ' ';
	return swar;
}

/*
struct edge_t {
	struct {
		int *_Nonnull source;
		int *_Nonnull target;
	};
	struct adj_list {
		adj_list *adj_list_next;
		int *_Nonnull target;
	};
	struct dfs_stack {
		adj_list *adj_list_next;
		dfs_stack *dfs_stack_prev;
	};
};
*/
struct edge_t {
	int first, second;
};

[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] constexpr int
cycle_detection(const int n, int *const vertex, edge_t *const edge) noexcept;

[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] int
main() noexcept {
	constexpr int max_size = 500'000;

#ifndef	MADV_HUGEPAGE
#define	MADV_HUGEPAGE MADV_NORMAL
#else
	alignas(2_Mi)
#endif
	static constinit struct {
		int vertex[max_size]{}; // MUST be completely cleared for correctness
		union {
			edge_t edge[max_size + 1];
			std::uint64_t os[];
			char output[];
		}; // CAN be completely uninitialized
	} storage{};
	::madvise(&storage, sizeof(storage), MADV_HUGEPAGE);
#ifndef	MADV_POPULATE_WRITE
#define	MADV_POPULATE_WRITE MADV_NORMAL
#endif
	::madvise(&storage, sizeof(storage), MADV_POPULATE_WRITE);
	const auto input = read_file(STDIN_FILENO);
	assert(!input.empty());
	auto c = input.begin();
	const auto last = input.end();
	const auto n = parse_int(c, last, ' ');
	assert(2 <= n and n <= max_size);
	const auto m = parse_int(c, last, '\n');
	assert(1 <= m and m <= max_size);
	const auto edge = storage.edge;
	const auto vertex = storage.vertex;
	{
		int i = 1;
		do {
			assert(i <= m);
			const auto u = parse_int(c, last, ' ');
			assert(0 <= u and u < n);
			edge[i].first = std::exchange(vertex[u], i);
			const auto v = parse_int(c, last, '\n');
			assert(0 <= v and v < n);
			assert(u != v);
			edge[i].second = v;
			++i;
		} while (c != last);
		assert(i == m + 1);
	}
	const auto cycle_length = cycle_detection(n, vertex, edge);
	if (cycle_length == 0) {
		const std::string_view s = "-1\n";
		::write(STDOUT_FILENO, s.data(), s.size());
		return 0;
	}
	assert(0 < cycle_length and cycle_length <= std::min(n, m));
	for (auto dfs_stack = edge->second, i = 0; i != cycle_length; ++i) {
		assert(0 < dfs_stack and dfs_stack <= m);
		vertex[i] = dfs_stack;
		dfs_stack = edge[dfs_stack].second;
	}
	auto os = storage.os;
	*os++ = swar2(cycle_length);
	for (int i = cycle_length; i-- != 0;) *os++ = swar2(vertex[i] - 1);
	assert(os == storage.os + cycle_length + 1);
	auto nbyte = (cycle_length + 1) * sizeof(*storage.os);
	while (storage.output[--nbyte] != '\n');
	::write(STDOUT_FILENO, storage.output, nbyte + 1);
	return 0;
}

constexpr int
cycle_detection(const int n, int *const vertex, edge_t *const edge) noexcept {
	constexpr auto source = [](const int v) constexpr noexcept {return -v - 1;};
	for (int dfs_stack = 0, i = 0; i != n; ++i) for (auto v = i, u = v;;) {
		assert(0 <= u and u < n);
		assert(0 <= v and v < n);
		if (vertex[v] == 0) {
			if (dfs_stack == 0) break;
			const auto [adj_list, dfs_stack_prev] = edge[dfs_stack];
			// TODO: free dfs_stack
			if (adj_list == 0) {
				v = u;
				u = source(vertex[u]);
				vertex[v] = 0;
				dfs_stack = dfs_stack_prev;
			} else {
				v = std::exchange(edge[adj_list].second, dfs_stack_prev);
				dfs_stack = adj_list;
			}
		} else if (vertex[v] > 0) {
			const auto adj_list = std::exchange(vertex[v], source(u));
			u = v;
			v = std::exchange(edge[adj_list].second, dfs_stack);
			dfs_stack = adj_list;
		} else {
			*edge = {0, dfs_stack};
			int cycle_length = 1;
			for (;u != v; u = source(vertex[u])) ++cycle_length;
			return cycle_length;
		}
	}
	return 0;
}

#if 1
// #else
template<int n, int m>
[[nodiscard, gnu::always_inline, gnu::no_stack_protector]] constexpr bool
cyclic(const std::span<const edge_t, m> pair) noexcept {
	int vertex[n]{};
	edge_t edge[m + 1];
	std::ranges::copy(pair, edge + 1);
	for (int i = 0; i++ != m;) {
		auto &u = edge[i].first;
		u = std::exchange(vertex[u], i);
	}
	return cycle_detection(n, vertex, edge) != 0;
}
static_assert(cyclic<5, 7>({{
	{0, 3}, {0, 4}, {4, 2}, {4, 3}, {4, 0}, {2, 1}, {1, 0},
}}));
static_assert(!cyclic<2, 1>({{
	{1, 0},
}}));
static_assert(cyclic<4, 6>({{
	{0, 1}, {1, 2}, {2, 0}, {0, 1}, {1, 3}, {3, 0},
}}));
#endif
