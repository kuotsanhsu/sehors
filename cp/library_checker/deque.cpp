#pragma	GCC optimize("O3")
#ifndef	DEBUG
#define	NDEBUG
#endif
// #define	NDEBUG
#include <cassert>
#include <bit>
#include <iterator>
#include <cstdint>
#include <cstddef>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>

namespace {

constexpr auto operator""_Ki(unsigned long long nbyte) noexcept {return nbyte << 10;}
constexpr auto operator""_Mi(unsigned long long nbyte) noexcept {return nbyte << 20;}

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
constexpr std::size_t page_size			= 4_Ki;		// _SC_PAGE_SIZE

constexpr std::uint64_t digit_mask = 0x3030'3030'3030'3030;

[[nodiscard, gnu::always_inline]] inline int
digit_count8(const char *const c) noexcept {
	const auto a = std::bit_cast<std::uint64_t>(*reinterpret_cast<const char(*)[8]>(c));
	static_assert(not('\n' & 0x30));
	static_assert('0' & 0x30);
	static_assert('9' & 0x30);
	const auto digit_count = std::countr_zero((a & digit_mask) ^ digit_mask) >> 3;
	assert(0 <= digit_count);
	assert(digit_count <= 8);
	return digit_count;
}

[[nodiscard, gnu::always_inline]] inline int
digit_count16(const char *const c) noexcept {
	const auto lo = digit_count8(c);
	const auto hi = digit_count8(c + 8);
	const auto lo_eq_8 = lo >> 3;
	const auto more = hi & -lo_eq_8;
	const auto result = lo + more;
	if (lo == 8) {
		assert(lo_eq_8 == 1);
		assert(more == hi);
		assert(result == lo + hi);
	} else {
		assert(lo_eq_8 == 0);
		assert(more == 0);
		assert(result == lo);
	}
	return result;
}

[[nodiscard, gnu::always_inline]] inline std::uint32_t
value6(const char *const c, const int length) noexcept {
	auto a = std::bit_cast<std::uint64_t>(*reinterpret_cast<const char(*)[8]>(c));
	a ^= digit_mask;
	a <<= ((8 - length) & 7) << 3; // safely yield garbage for length > 8
	a >>= 2 << 3;
	a = a * 10 + (a >> 8);
	const auto a0145 = (a & 0xff'0000'00ff) * ((1'0000ULL << 32) + 1);
	const auto a23 = (a & 0xff'0000) * (100ULL << 16);
	return static_cast<std::uint32_t>((a0145 + a23) >> 32);
}

} // namespace

extern "C" void __gxx_personality_v0() { __builtin_trap(); }

[[gnu::no_stack_protector]] int
main() {
	constexpr std::size_t query_limit = 500'000;
	constexpr std::size_t deque_size = 1UZ << 19;
	static_assert(query_limit < deque_size);
	constexpr std::size_t deque_mask = deque_size - 1;

#ifndef	MADV_HUGEPAGE
#define	MADV_HUGEPAGE MADV_NORMAL
#else
	alignas(2_Mi)
#endif
#ifndef	MADV_POPULATE_WRITE
#define	MADV_POPULATE_WRITE MADV_NORMAL
#endif
	static struct {
		alignas(page_size) int deque[deque_size];
		alignas(page_size) char output[level2_cache_size];
	} storage;
	if (::madvise(&storage, sizeof(storage), MADV_HUGEPAGE) == -1) [[unlikely]] return 2;
	if (::madvise(&storage, sizeof(storage), MADV_POPULATE_WRITE) == -1) [[unlikely]] return 3;

	struct ::stat st;
	if (::fstat(STDIN_FILENO, &st) == -1) [[unlikely]] return 1;
	const std::size_t input_size = st.st_size;
	if (input_size == 0) [[unlikely]] return 1;
#ifndef	MAP_POPULATE
#define	MAP_POPULATE MAP_FILE
#endif
	const auto input = static_cast<const char *>(::mmap(nullptr, input_size, PROT_READ,
		MAP_PRIVATE | MAP_POPULATE,
		STDIN_FILENO, 0)); // do NOT care about reading out of bounds later
	if (input == MAP_FAILED) [[unlikely]] return 1;
	int a = 0, b = 0;

	const auto Q_digit_count = digit_count8(input + a);
	auto Q = value6(input + a, Q_digit_count);
	assert(1 <= Q && Q <= query_limit);
	a += Q_digit_count + 1;

	constexpr auto buffer_threshold = std::size(storage.output) - 16;
	for (int deque_begin = 0, deque_end = 0; Q--;) {
		const auto op = input[a] - '0';
		assert(0 <= op);
		assert(op <= 4);
		a += 2;
		const auto digit_count = digit_count16(input + a);
		{
			const auto x = (a << 4) ^ (digit_count & 15);
			const auto op_eq_13 = op & 1;
			const auto front = deque_begin - 1, back = deque_end;
			const auto j = front ^ ((front ^ back) & -op_eq_13);
			assert(j == (op == 1 or op == 3 ? back : front));
			storage.deque[j & deque_mask] = x;
		}
		{
			static constexpr std::int8_t begin_advance[5] = {-1, 0, 1};
			deque_begin += begin_advance[op];
		}
		{
			static constexpr std::int8_t end_advance[5] = {0, 1, 0, -1};
			deque_end += end_advance[op];
		}
		{
			const auto op_eq_4 = op >> 2;
			assert(op == 4 == op_eq_4);
			const auto i = value6(input + a, digit_count);
			const auto j = (deque_begin + i) & -op_eq_4;
			assert(op == 4 or j == 0);
			const auto x = storage.deque[j & deque_mask];
			const auto offset = (x >> 4) & -op_eq_4;
			assert(op == 4 or offset == 0);
			__builtin_memcpy(storage.output + b, input + offset, 16);
			const auto length = ((x & 15) + 1) & -op_eq_4;
			assert(op == 4 != (length == 0));
			b += length;
		}
		if (b >= buffer_threshold) [[unlikely]] {
			(void)::write(STDOUT_FILENO, storage.output, b);
			b = 0;
		}
		const auto op_eq_014 = ((op & 2) >> 1) ^ 1;
		assert(op_eq_014 == (op == 0 or op == 1 or op == 4));
		a += (digit_count + 1) & -op_eq_014;
	}
	assert(a == input_size);
	(void)::write(STDOUT_FILENO, storage.output, b);
	::_exit(0);
}

constexpr std::size_t max_input_size = 5827894, max_output_size = 4744724;
static_assert(max_input_size < (1UZ << 23));
static_assert(max_output_size < (1UZ << 23));
