#pragma GCC optimize "Ofast"
// #define	DEBUG
#ifndef	DEBUG
#define	NDEBUG
#endif
// #define	NDEBUG
#include <cassert>
#include <bit>
#include <utility>
#include <iterator>
#include <array>
#include <algorithm>
#include <print>
#include <cstring>
#include <cstdint>
#include <cstddef>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>

constexpr std::uint64_t digit_mask = 0x3030'3030'3030'3030;

[[nodiscard, gnu::always_inline]] int digit_count10(const char *const c) noexcept {
	const auto digit_count8 = [](const char *const c) constexpr noexcept {
		std::uint64_t a;
		static_assert(sizeof(a) == 8);
		(void)std::memcpy(&a, c, 8);
		const auto digit_count = std::countr_zero((a & digit_mask) ^ digit_mask) >> 3;
		assert(0 <= digit_count and digit_count <= 8);
		return digit_count;
		static_assert(not('\n' & 0x30));
		static_assert('0' & 0x30);
		static_assert('9' & 0x30);
	};
	auto digit_count = digit_count8(c);
	assert(1 <= digit_count);
	if (digit_count == 8) digit_count += digit_count8(c + 8);
	assert(digit_count <= 10);
	return digit_count;
	
}

[[nodiscard, gnu::always_inline]] int parse6(const char *&c) noexcept {
	std::uint64_t a;
	static_assert(sizeof(a) == 8);
	(void)std::memcpy(&a, c, 8);
	const auto digit_count = std::countr_zero((a & digit_mask) ^ digit_mask) >> 3;
	assert(1 <= digit_count and digit_count <= 6);
	c += digit_count;
	assert(*c == '\n');

	a ^= digit_mask;
	a <<= (8 - digit_count) << 3;
	a >>= 2 << 3;
	const auto d = std::bit_cast<std::array<char, 8>>(a);
	a = a * 10 + (a >> 8);
	assert(a == std::bit_cast<uint64_t>(std::array<char, 8>{
		static_cast<char>(d[0] * 10 + d[1]), // a0145
		static_cast<char>(d[1] * 10 + d[2]),
		static_cast<char>(d[2] * 10 + d[3]), // a23
		static_cast<char>(d[3] * 10 + d[4]),
		static_cast<char>(d[4] * 10 + d[5]), // a0145
		static_cast<char>(d[5] * 10),
	}));
	const auto a0145 = (a & 0xff'0000'00ff) * ((1'0000ULL << 32) + 1);
	assert(a0145 == std::bit_cast<uint64_t>(std::array<int, 2>{
		d[0] * 10 + d[1],
		d[0] * 10'0000 + d[1] * 1'0000 + d[4] * 10 + d[5],
	}));
	const auto a23 = (a & 0xff'0000) * (100 << 16);
	assert(a23 == std::bit_cast<uint64_t>(std::array<int, 2>{
		0,
		d[2] * 1000 + d[3] * 100,
	}));
	const auto result = static_cast<std::int32_t>((a0145 + a23) >> 32);
	assert(result == d[0] * 10'0000 + d[1] * 1'0000 + d[2] * 1000 + d[3] * 100 + d[4] * 10 + d[5]);
	return result;
}

int main() noexcept {
	struct ::stat st;
	if (::fstat(STDIN_FILENO, &st) == -1) [[unlikely]] return 1;
	const std::size_t input_size = st.st_size;
	if (input_size == 0) [[unlikely]] return 1;
#ifndef	MAP_POPULATE
#define	MAP_POPULATE MAP_FILE
#endif
	const auto input = static_cast<const char *>(::mmap(
		nullptr, input_size, PROT_READ, MAP_PRIVATE | MAP_POPULATE, STDIN_FILENO, 0
	));
	if (input == MAP_FAILED) [[unlikely]] return 1;
	auto c = input, last = input + input_size;

	constexpr int query_limit = 500'000;
	constexpr int deque_size = 1 << 20;
	static_assert(query_limit * 2 <= deque_size);
	static int deque[deque_size];
	auto deque_begin = deque + query_limit, deque_end = deque_begin;

	constexpr int offset_shift = 4;
	static_assert(10 < (1 << offset_shift));
	const auto x = [input, &c] constexpr noexcept {
		const auto length = digit_count10(c);
		const auto offset = c - input;
		c += length;
		return offset << offset_shift ^ length;
	};

	// c += digit_count10(c);
	const auto Q = parse6(c);
	assert(1 <= Q and Q <= query_limit);
	for (;;) {
		assert(c < last);
		assert(*c == '\n');
		if (++c == last) break;
		switch(*c++) {
		case '0':
			assert(*c == ' ');
			++c;
			assert(std::begin(deque) < deque_begin);
			*--deque_begin = x();
			break;
		case '1':
			assert(*c == ' ');
			++c;
			assert(deque_end < std::end(deque));
			*deque_end++ = x();
			break;
		case '2':
			assert(deque_begin < deque_end);
			++deque_begin;
			break;
		case '3':
			assert(deque_begin < deque_end);
			--deque_end;
			break;
		case '4': {
			assert(*c == ' ');
			++c;
			const auto i = parse6(c);
			assert(0 <= i and deque_begin + i < deque_end);
			const auto x = deque_begin[i];
			const auto offset = x >> offset_shift;
			const auto length = x & ((1 << offset_shift) - 1);
			assert(input[offset + length] == '\n');
			::write(STDOUT_FILENO, input + offset, length + 1);
		}	break;
		default:
			assert(false);
			std::unreachable();
		}
	}
}
