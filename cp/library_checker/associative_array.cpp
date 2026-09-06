#pragma GCC optimize "Ofast"

#ifndef	DEBUG
#define	NDEBUG
#endif

#include <cassert>
#include <iostream>
#include <unordered_map>

int main() {
	std::cin.tie(nullptr)->sync_with_stdio(false);
	constexpr long long query_limit = 1'000'000;
	constexpr long long key_value_limit = 1'000'000'000'000'000'000;
	int Q;
	std::cin >> Q;
	assert(1 <= Q and Q <= query_limit);
	for (std::unordered_map<long long, long long> m; Q--;) {
		char c;
		long long k;
		std::cin >> c >> k;
		assert(0 <= k and k <= key_value_limit);
		if (c == '0') {
			long long v;
			std::cin >> v;
			assert(0 <= v and v <= key_value_limit);
			m[k] = v;
		} else {
			assert(c == '1');
			const auto node = m.find(k);
			if (node == m.end()) std::cout << "0\n";
			else std::cout << node->second << '\n';
		}
	}
}
