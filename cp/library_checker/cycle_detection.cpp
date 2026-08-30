// make CXXFLAGS='-std=c++23 -g -DDEBUG' cycle_detection && ./cycle_detection
// make CXXFLAGS='-std=c++23 -O2' cycle_detection &&
// 	for i in {1..3}; do ./cycle_detection < sample$i.txt; done
#ifndef DEBUG
#	define NDEBUG
#endif

#if defined(__clang__) && __has_feature(nullability)
#else
#	define _Nonnull
#endif

#include <assert.h>
#include <stdio.h>

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
	unsigned length;
	//union vertex *root;
	struct edge::dfs_stack *dfs_stack;
};

[[nodiscard]] struct cycle
cycle_detection(const unsigned n, const unsigned m, union edge edge[], union vertex vertex[]) {
	assert((void*)edge < (void*)vertex);
	for (unsigned i = 0; i != m; ++i) {
		const auto e = edge + i;
		assert(e->adj_list.vertex == e->target);
		const auto v = e->source;
		e->adj_list.next = v->adj_list;
		v->adj_list = &e->adj_list;
	}
	
	assert(fprintf(stderr, "adjacency list:\n"));
	for (unsigned i = 0; i != n; ++i) {
		assert(fprintf(stderr, "[%u]", i));
		for (auto adj_list = vertex[i].adj_list; adj_list; adj_list = adj_list->next) {
			assert(fprintf(stderr, " %ld", adj_list->vertex - vertex));
		}
		assert(fprintf(stderr, "\n"));
	}

	assert(fprintf(stderr, "dfs trace:\n"));
	struct edge::dfs_stack *dfs_stack = nullptr;
	for (unsigned i = 0; i != n; ++i) for (auto v = vertex + i, u = v;;) {
		assert(fprintf(stderr, "[%ld->%ld]", u - vertex, v - vertex));
		for (unsigned i = 0; i != n; ++i) {
			const auto v = vertex[i];
			if (v.adj_list == nullptr) assert(fprintf(stderr, " 0"));
			else if (v.source < vertex) assert(fprintf(stderr, " *"));
			else assert(fprintf(stderr, " %ld", v.source - vertex));
		}
		assert(fprintf(stderr, "\n"));

		if (v->adj_list == nullptr) {
			if (dfs_stack == nullptr) break;
			const auto adj_list = dfs_stack->adj_list;
			// TODO: free dfs_stack
			if (adj_list == nullptr) {
				v = u;
				u = u->source;
				v->adj_list = nullptr;
				dfs_stack = dfs_stack->prev;
			} else {
				v = adj_list->vertex;
				const auto new_dfs_stack = &((union edge*)adj_list)->dfs_stack;
				new_dfs_stack->prev = dfs_stack->prev;
				dfs_stack = new_dfs_stack;
			}
		} else if (v->source < vertex) {
			const auto adj_list = v->adj_list;
			v->source = u;
			u = v;
			v = adj_list->vertex;
			const auto new_dfs_stack = &((union edge*)adj_list)->dfs_stack;
			new_dfs_stack->prev = dfs_stack;
			dfs_stack = new_dfs_stack;
		} else {
			unsigned cycle_length = 0;
			const auto root = v->source = u;
			struct edge::dfs_stack *q = nullptr, *p = dfs_stack;
			do {
				++cycle_length;
				const auto r = p->prev;
				p->prev = q;
				q = p;
				p = r;
				u = u->source; /*
				const auto w = u->source;
				u->source = v;
				v = u;
				u = w;
				//*/
			} while (u != root);
			// TODO: for (; p; p = p->prev) { /* free p */ }
			assert(dfs_stack->prev == nullptr);
			dfs_stack->prev = q;
			return (struct cycle){.length=cycle_length, .dfs_stack=dfs_stack};
		}
	}
	return (struct cycle){};
}

struct pair {
	unsigned u, v;
};
static_assert(sizeof(struct pair) == 8);

[[nodiscard]] bool
test(const char *const name,
	const unsigned n, const unsigned m, union edge edge[], union vertex vertex[],
	const struct pair pair[], const bool acyclic
) {
	assert(fprintf(stderr, "=== %s ===\n", name));
	assert(2 <= n);
	assert(1 <= m);
	assert((void*)nullptr < (void*)edge);
	assert((void*)edge < (void*)vertex);
	for (unsigned i = 0; i != m; ++i) {
#ifndef NDEBUG
		const auto u = pair[i].u, v = pair[i].v;
#else
		unsigned u, v;
		scanf("%u %u", &u, &v);
#endif
		assert(0 <= u && u < n);
		assert(0 <= v && v < n);
		assert(u != v);
		edge[i].source = vertex + u;
		edge[i].target = vertex + v;
	}

	const auto cycle = cycle_detection(n, m, edge, vertex);
	const auto empty_cycle = cycle.length == 0;
	assert(empty_cycle == (cycle.dfs_stack == nullptr));
	if (empty_cycle) {
		printf("-1\n");
		return acyclic;
	}
#ifndef NDEBUG
	else if (acyclic) return false;
	assert(empty_cycle == acyclic);
#endif

	auto cycle_length = cycle.length;
	printf("%u\n", cycle_length);
	auto p = cycle.dfs_stack;
#ifndef NDEBUG
	auto v = pair[(union edge*)p - edge].v;
#endif
	do {
		p = p->prev;
		const auto i = (union edge*)p - edge;
		printf("%ld\n", i);
#ifndef NDEBUG
		if (v != pair[i].u) return false;
		v = pair[i].v;
#endif
		--cycle_length;
	} while (p != cycle.dfs_stack);
	assert(cycle_length == 0);
	return true;
}

[[nodiscard]] bool sample1();
[[nodiscard]] bool sample2();
[[nodiscard]] bool sample3();

int main() {
	assert(sample1());
	assert(sample2());
	assert(sample3());
#ifndef NDEBUG
	return 0;
#endif
	constexpr unsigned max_size = 500'000;
	static struct {
		union edge edge[max_size];
		union vertex vertex[max_size];
	} zone;
	unsigned n, m;
	scanf("%u %u", &n, &m);
	return !test(nullptr, n, m, zone.edge, zone.vertex, nullptr, true);
}

bool
sample1() {
	constexpr unsigned n = 5, m = 7;
	static struct {
		union edge edge[m];
		union vertex vertex[n];
	} zone;
	constexpr struct pair pair[m] = {{0, 3}, {0, 4}, {4, 2}, {4, 3}, {4, 0}, {2, 1}, {1, 0}};
	return test(__func__, n, m, zone.edge, zone.vertex, pair, false);
}

bool
sample2() {
	constexpr unsigned n = 2, m = 1;
	static struct {
		union edge edge[m];
		union vertex vertex[n];
	} zone;
	constexpr struct pair pair[m] = {{1, 0}};
	return test(__func__, n, m, zone.edge, zone.vertex, pair, true);
}

bool
sample3() {
	constexpr unsigned n = 4, m = 6;
	static struct {
		union edge edge[m];
		union vertex vertex[n];
	} zone;
	constexpr struct pair pair[m] = {{0, 1}, {1, 2}, {2, 0}, {0, 1}, {1, 3}, {3, 0}};
	return test(__func__, n, m, zone.edge, zone.vertex, pair, false);
}
