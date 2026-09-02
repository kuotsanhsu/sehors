// make CXXFLAGS='-std=c++23 -g -DDEBUG' cycle_detection && ./cycle_detection
// make CXXFLAGS='-std=c++23 -O2' cycle_detection &&
// 	for i in {1..3}; do ./cycle_detection < sample$i.txt; done
// #define DEBUG
#ifdef DEBUG
#	include <algorithm>
#else
#	define NDEBUG
#endif

#include <cassert>
#include <utility>
#include <string_view>
#include <span>
#include <charconv>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>

/*
struct edge {
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
using edge_t = std::pair<int, int>;

[[nodiscard]] constexpr int source(const int v) noexcept {return -v - 1;}

[[nodiscard]] constexpr int cycle_detection(edge_t edge[], int vertex[]) noexcept {
	const auto [n, m] = edge[0];
	assert(2 <= n);
	assert(1 <= m);
	for (int i = 0; i++ != m;) {
		auto &[u, v] = edge[i];
		assert(0 <= u && u < n);
		assert(0 <= v && v < n);
		assert(u != v);
		u = std::exchange(vertex[u], i);
	}
	for (int dfs_stack = 0, i = 0; i != n; ++i) for (int v = i, u = v;;) {
		assert(0 <= u);
		assert(0 <= v);
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
			const int adj_list = std::exchange(vertex[v], source(u));
			u = v;
			v = std::exchange(edge[adj_list].second, dfs_stack);
			dfs_stack = adj_list;
		} else {
			edge[0] = {0, dfs_stack};
			int cycle_length = 1;
			for (;u != v; u = source(vertex[u])) ++cycle_length;
			return cycle_length;
		}
	}
	return 0;
}

[[nodiscard]] std::string_view read_file(const int fd) noexcept {
	constexpr int mmap_flags = MAP_SHARED
#ifdef MAP_POPULATE
		| MAP_POPULATE
#endif
#ifdef MAP_RESILIENT_CODESIGN
		| MAP_RESILIENT_CODESIGN
#endif
#ifdef MAP_RESILIENT_MEDIA
		| MAP_RESILIENT_MEDIA
#endif
	;
	struct ::stat stat;
	if (::fstat(fd, &stat) == -1) return {};
	const std::size_t data_size = stat.st_size;
	if (data_size == 0) return {};
	void *const data = ::mmap(nullptr, data_size, PROT_READ, mmap_flags, fd, 0);
	if (data == MAP_FAILED) return {};
	::madvise(data, data_size, MADV_SEQUENTIAL); // hint-only; don't care about failure
	return {static_cast<const char*>(data), data_size};
}

void read_ints(std::span<int> is, std::string_view s) noexcept {
	auto i = is.begin();
	bool fresh = true; // -Wunused-but-set-variable MUST warn if NDEBUG
	for (int n = 0; const char c : s) {
		if ('0' <= c) {
			assert(c <= '9');
			n *= 10;
			n += c - '0';
			fresh = false;
		} else [[unlikely]] {
			assert(!fresh);
			assert(c == '\n' || c == ' ');
			assert(i < is.end());
			*i++ = n;
			n = 0;
			fresh = true;
		}
	}
	assert(fresh || i++ < is.end()); // if (!fresh) assert(i++ < is.end());
	assert(i <= is.end());
	assert(is.begin() + 1 < i);
	const int m = is[1]; // -Wunused-but-set-variable MUST warn if NDEBUG
	assert(is.begin() + 2 * (m + 1) == i);
}

class write_ints {
	char *first, *c, *const last;
public:
	constexpr write_ints(std::span<char> buffer) noexcept
		: first(buffer.data()), c(first), last(first + buffer.size()) {}

	[[nodiscard]] constexpr bool operator()(const int value) noexcept {
		const auto [ptr, ec] = std::to_chars(c, last, value);
		if (ec == std::errc::value_too_large) [[unlikely]] {
			assert(ptr == last);
			return false;
		}
		assert(ec == std::errc());
		c = ptr;
		assert(c < last);
		*c++ = '\n';
		return true;
	}

	[[nodiscard]] int flush() noexcept {
		assert(c <= last);
		while (first != c) {
			assert(first < c);
			const ::ssize_t nbyte = ::write(STDOUT_FILENO, first, c - first);
			if (nbyte == -1) [[unlikely]] {
				if (errno == EINTR) continue;
				assert(errno != 0);
				return errno;
			}
			assert(nbyte > 0);
			first += nbyte;
		}
		return 0;
	}
};

[[nodiscard]] constexpr std::size_t total_digits_before(std::size_t upper_bound) noexcept {
	if (upper_bound == 0) return 0;
	std::size_t total = 1, digits = 1, a = 1, b = 10;
	while (b <= upper_bound) {
		assert(a <= b);
		total += (b - a) * digits;
		a = b;
		b *= 10; // FIXME: infinite loop if b overflows
		++digits;
	}
	assert(a <= upper_bound);
	return total + (upper_bound - a) * digits;
}

int main() {
	constexpr std::size_t max_size = 500'000, edge_size = max_size + 1;
	static constinit union {
		edge_t edge[edge_size];
		int is[edge_size * 2];
		char output[edge_size * 8];
	} storage{};
	static_assert(sizeof(storage.edge) == sizeof(storage.is));
	static_assert(sizeof(storage.is) == sizeof(storage.output));
	constexpr std::size_t total_digits = total_digits_before(500'000);
	static_assert(total_digits == 2'888'890);
	static_assert(sizeof(storage.output) >= 6 + 1 + total_digits + max_size);
	read_ints(storage.is, read_file(STDIN_FILENO));
	edge_t *edge = storage.edge;
	const auto [n, m] = *edge;
	static constinit int vertex[max_size]{};
	const int cycle_length = cycle_detection(edge, vertex);
	write_ints println(storage.output);
	if (cycle_length == 0) {
		assert(*edge == std::make_pair(n, m));
		if (!println(-1)) return 1;
	} else {
		assert(0 < cycle_length && cycle_length <= std::min(n, m));
		for (int dfs_stack = edge->second, i = 0; i != cycle_length; ++i) {
			assert(0 < dfs_stack && dfs_stack <= m);
			vertex[i] = dfs_stack;
			dfs_stack = edge[dfs_stack].second;
		}
		if (!println(cycle_length)) return 1;
		for (int i = cycle_length; i-- != 0;) if (!println(vertex[i] - 1)) return 1;
	}
	if (println.flush() != 0) return 2;
	return 0;
}

#ifdef DEBUG
template<int n, int m>
[[nodiscard]] constexpr bool cyclic(std::span<const edge_t, m> pair) noexcept {
	edge_t edge[m + 1] = {{n, m},};
	std::ranges::copy(pair, edge + 1);
	int vertex[n]{};
	return cycle_detection(edge, vertex) != 0;
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
