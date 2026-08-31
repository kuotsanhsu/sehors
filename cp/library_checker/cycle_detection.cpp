// make CXXFLAGS='-std=c++23 -g -DDEBUG' cycle_detection && ./cycle_detection
// make CXXFLAGS='-std=c++23 -O2' cycle_detection &&
// 	for i in {1..3}; do ./cycle_detection < sample$i.txt; done
#ifndef DEBUG
#	define NDEBUG
#endif

#include <cassert>
#include <iterator>
#include <iostream>

using edge = std::pair<int, int>;
static_assert(sizeof(edge) == 8);

/*
union vertex;

union edge {
	struct {
		union vertex *_Nonnull source;
		union vertex *_Nonnull target;
	};
	struct adj_list {
		struct adj_list *next;
		union vertex *_Nonnull vertex;
	} adj_list;
	struct dfs_stack {
		struct adj_list *adj_list;
		struct dfs_stack *prev;
	} dfs_stack;
};
static_assert(sizeof(union edge) == 16);

union vertex {
	struct edge::adj_list *adj_list;
	union vertex *_Nonnull source;
};
static_assert(sizeof(union vertex) == 8);

struct cycle {
	int length;
	struct edge::dfs_stack *dfs_stack;
};
*/

[[nodiscard]] constexpr int source(const int v) noexcept {return -v - 1;}

[[nodiscard]] constexpr edge
cycle_detection(const int n, const int m, edge edge[], int vertex[]) noexcept {
	for (int i = 0; i++ != m;) {
		const int u = edge[i].first;
		edge[i].first = vertex[u];
		vertex[u] = i;
	}
	for (int dfs_stack = 0, i = 0; i != n; ++i) for (int v = i, u = v;;) {
		if (vertex[v] == 0) {
			if (dfs_stack == 0) break;
			const int adj_list = edge[dfs_stack].first;
			// TODO: free dfs_stack
			if (adj_list == 0) {
				v = u;
				assert(vertex[u] < 0);
				u = source(vertex[u]);
				vertex[v] = 0;
				dfs_stack = edge[dfs_stack].second;
			} else {
				v = edge[adj_list].second;
				edge[adj_list].second = edge[dfs_stack].second;
				dfs_stack = adj_list;
			}
		} else if (vertex[v] > 0) {
			const int adj_list = vertex[v];
			vertex[v] = source(u);
			u = v;
			v = edge[adj_list].second;
			edge[adj_list].second = dfs_stack;
			dfs_stack = adj_list;
		} else {
			vertex[v] = source(u);
			const int root = u;
			int cycle_length = 0, q = 0, p = dfs_stack;
			do {
				++cycle_length;
				const int r = edge[p].second;
				edge[p].second = q;
				q = p;
				p = r;
				u = source(vertex[u]);
			} while (u != root);
			// TODO: for (; p; p = p->prev) { /* free p */ }
			assert(edge[dfs_stack].second == 0);
			edge[dfs_stack].second = q;
			return {cycle_length, dfs_stack};
		}
	}
	return {};
}

[[nodiscard]] constexpr bool
cyclic(const int n, const int m, edge edge[], int vertex[],
	std::input_iterator auto pair, std::output_iterator<int> auto output
) noexcept {
	assert(2 <= n);
	assert(1 <= m);
	for (int i = 0; i++ != m;) {
		const ::edge p = *pair++;
		const auto [u, v] = p;
		assert(0 <= u && u < n);
		assert(0 <= v && v < n);
		assert(u != v);
		edge[i] = {u, v};
	}

	auto [cycle_length, dfs_stack] = cycle_detection(n, m, edge, vertex);
	if (cycle_length == 0) {
		assert(dfs_stack == 0);
		*output++ = -1;
		return false;
	}
	assert(dfs_stack != 0);

	*output++ = cycle_length;
	int p = dfs_stack;
	do {
		p = edge[p].second;
		*output++ = p - 1;
		--cycle_length;
	} while (p != dfs_stack);
	assert(cycle_length == 0);
	return true;
}

namespace std {
istream& operator>>(istream &is, edge &p) {return is >> p.first >> p.second;}
}

int main() {
	std::cin.tie(nullptr)->sync_with_stdio(false);
	constexpr int max_size = 500'000;
	static struct {
		::edge edge[max_size + 1];
		int vertex[max_size]{};
	} zone;
	std::ostream_iterator<int> output(std::cout, "\n");
	std::istream_iterator<edge> pair(std::cin);
	const auto [n, m] = *pair++;
	(void)cyclic(n, m, zone.edge, zone.vertex, pair, output);
}

template<typename T> struct noop_output_iterator {
	using iterator_category = std::output_iterator_tag;
	using difference_type = std::ptrdiff_t;
	constexpr noop_output_iterator& operator=(const T&) noexcept {return *this;}
	constexpr noop_output_iterator& operator=(T&&) noexcept {return *this;}
	constexpr noop_output_iterator& operator*() noexcept {return *this;}
	constexpr noop_output_iterator& operator++() noexcept {return *this;}
	constexpr noop_output_iterator operator++(int) const noexcept {return *this;}
};

static_assert(std::output_iterator<noop_output_iterator<int>, int>);

template<int n, int m> [[nodiscard]] constexpr bool
sample(const std::array<edge, m> pair) noexcept {
	struct {
		::edge edge[m + 1];
		int vertex[n]{};
	} zone;
	noop_output_iterator<int> output;
	return cyclic(n, m, zone.edge, zone.vertex, pair.begin(), output);
}

static_assert(sample<5, 7>(std::array<edge, 7>{{{0, 3}, {0, 4}, {4, 2}, {4, 3}, {4, 0}, {2, 1}, {1, 0}}}));
static_assert(!sample<2, 1>(std::array<edge, 1>{{{1, 0}}}));
static_assert(sample<4, 6>(std::array<edge, 6>{{{0, 1}, {1, 2}, {2, 0}, {0, 1}, {1, 3}, {3, 0}}}));
