#pragma GCC optimize "Ofast"

#ifndef	DEBUG
#	define	NDEBUG
#endif
// #define	NDEBUG

#include <cassert>
#include <cctype>
#include <iostream>
#include <print>
#include <ranges>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

int main() {
	std::cin.tie(nullptr)->sync_with_stdio(false);
	std::size_t N;
	const auto S = std::ranges::to<std::vector<std::string>>(
		std::ranges::istream_view<std::string>(std::cin >> N)
	);
	assert((std::println(stderr, "S={}", S), true));
	{ // Constraints.
		constexpr std::size_t limit = 1'000'000;
		assert(1 <= N and N <= limit);
		assert(S.size() == N);
		std::size_t total_length = 0;
		for (const std::string_view s : S) {
			assert(1 <= s.size());
			// assert(s.size() <= limit);
			total_length += s.size();
			for (const auto c : s) assert(std::islower(c));
		}
		// assert(1 <= total_length);
		assert(total_length <= limit);
	}

	std::unordered_map<std::string_view, std::size_t> P;
	std::vector<std::string_view> str;
	for (const std::string_view s : S) for (std::size_t j = 0; j <= s.size(); ++j) {
		const auto Pij = s.substr(0, j);
		const auto newly_added = P.try_emplace(Pij, str.size()).second;
		if (newly_added) str.push_back(Pij);
	}
	assert((std::println(stderr, "P={}", P), true));
	assert((std::println(stderr, "str={}", str), true));
	const auto n = P.size();
	assert(str.size() == n);
	assert(1 <= n);
	assert(P.at("") == 0);
	assert(str.at(0) == "");
	for (const auto [s, v] : P) assert(s == str[v]);

	const auto parent = [&P, &str](std::size_t v)-> std::size_t {
		// The zeroth vertex (the empty string) is the root and has no parent.
		assert(1 <= v);
		const auto s = str.at(v);
		assert(1 <= s.size());
		return P[s.substr(0, s.size() - 1)];
	};

	const auto suffix_link_destination = [&P, &str](std::size_t v)-> std::size_t {
		// The zeroth vertex (the empty string) cannot have a proper suffix, i.e. a suffix
		// that isn't the string itself.
		assert(1 <= v);
		const auto s = str.at(v);
		assert(1 <= s.size());
		for (std::size_t j = 1; j <= s.size(); ++j) {
			const auto suffix = s.substr(j);
			if (const auto it = P.find(suffix); it != P.end()) return it->second;
		}
		// A non-empty string will always have a proper suffix, e.g. the empty string, so
		// this line SHOULD be unreachable.
		assert(false);
		std::unreachable();
	};

	std::println("{}", n);
	for (std::size_t v = 1; v < n; ++v) std::println("{} {}", parent(v), suffix_link_destination(v));
	for (bool whitespace = false; const std::string_view s : S) {
		if (whitespace) [[likely]] std::print(" ");
		else whitespace = true;
		std::print("{}", P.at(s));
	}
	std::println("");
}
