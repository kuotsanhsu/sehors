#include <charconv>
#include <cstdio>
#include <print>
#pragma GCC optimize "Ofast"

#ifndef	DEBUG
#define	NDEBUG
#endif
// #define NDEBUG

#include <cassert>
#include <string_view>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>

using key_value_t = unsigned long long;

[[nodiscard]] constexpr key_value_t splitmix64(key_value_t x) noexcept {
	x += 0x9e3779b97f4a7c15ULL;
	x ^= x >> 30;
	x *= 0xbf58476d1ce4e5b9ULL;
	x ^= x >> 27;
	x *= 0x94d049bb133111ebULL;
	x ^= x >> 31;
	return x;
}

int main() {
	struct ::stat st;
	if (::fstat(STDIN_FILENO, &st) == -1) [[unlikely]] return 1;
	const std::size_t input_size = st.st_size;
	if (input_size == 0) [[unlikely]] return 1;
#ifndef MAP_POPULATE
#define MAP_POPULATE MAP_FILE
#endif
	const auto input = static_cast<const char *>(::mmap(
		nullptr, input_size, PROT_READ, MAP_PRIVATE | MAP_POPULATE, STDIN_FILENO, 0
	));
	if (input == MAP_FAILED) [[unlikely]] return 1;
	const auto last = input + input_size;

	constexpr int query_limit = 1'000'000;
	constexpr key_value_t key_value_limit = 1'000'000'000'000'000'000;
	int Q;
	auto c = std::from_chars(input, last, Q).ptr; // TODO: SWAR or AVX2: *c & '0'
	assert(1 <= Q and Q <= query_limit);
	assert((std::println(stderr, "{}", Q), true));
	
	constexpr int table_size = 1 << 20, table_mask = table_size - 1;
	static_assert(query_limit <= table_size);
	static constinit key_value_t key_table[table_size]{};
	static constinit int value_table[table_size];
	while (Q--) {
		assert(*c == '\n');
		assert(c[2] == ' ');
		const auto first = c += 3;
		key_value_t k;
		c = std::from_chars(first, last, k).ptr;
		assert(0 <= k and k <= key_value_limit);
		assert((std::print(stderr, "{} {}", first[-2], k), true));
		auto i = splitmix64(++k) & table_mask;
		if (*c == ' ') {
			assert(first[-2] == '0');
			const auto first = ++c;
			key_value_t v;
			c = std::from_chars(first, last, v).ptr;
			assert(0 <= v and v <= key_value_limit);
			assert((std::println(stderr, " {}", v), true));
			for (;; ++i, i &= table_mask) {
				auto &kk = key_table[i];
				if (kk == 0) {
					kk = k;
					break;
				} else if (kk == k) break;
			}
			static_assert(8 + (2 + 20 + 20) * query_limit < (1 << 26));
			const auto offset = first - input;
			assert(offset < (1 << 26));
			static_assert(26 < (1 << 5));
			const auto length = c - first;
			assert(length < (1 << 5));
			static_assert(26 + 5 < 32);
			value_table[i] = (offset << 5) | length;
		} else {
			assert(first[-2] == '1');
			assert((std::println(stderr, ""), true));
			for (;; ++i, i &= table_mask) {
				const auto kk = key_table[i];
				if (kk == 0) {
					assert(value_table[i] == 0);
					std::println("0");
					break;
				} else if (kk == k) {
					const auto v = value_table[i];
					assert(v != 0);
					const std::string_view s(input + (v >> 5), v & 31);
					std::println("{}", s);
					break;
				}
			}
		}
	}
}
