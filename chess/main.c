/*******************************************************************************

- https://en.wikipedia.org/wiki/Chess
- https://www.overleaf.com/learn/latex/Chess_notation

## Forsyth-Edwards Notation (FEN)
- White pieces are identified by uppercase letters (PNBRQK).
- Black pieces are identified by lowercase letters (pnbrqk).

*******************************************************************************/

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

struct board {
	uint64_t white, black, pawn, rook, knight, bishop, queen, king;
};

bool
board_invariant(struct board *board) {
	uint64_t occupancy = 0;
	if (occupancy & board->pawn)	return false;
	occupancy |= board->pawn;
	if (occupancy & board->rook)	return false;
	occupancy |= board->rook;
	if (occupancy & board->knight)	return false;
	occupancy |= board->knight;
	if (occupancy & board->bishop)	return false;
	occupancy |= board->bishop;
	if (occupancy & board->queen)	return false;
	occupancy |= board->queen;
	if (occupancy & board->king)	return false;
	occupancy |= board->king;
	if (__builtin_popcountg(occupancy) > 8 * 4) return false;
	if (board->white & board->black) return false;
	return (board->white | board->black) == occupancy;
}

void
board_init(struct board *board) {
	constexpr uint64_t first_rank = 0x0101'0101'0101'0101;
	constexpr uint64_t last_ranks = 0b1000'0001;
	board->white	= 0b0000'0011 * first_rank;
	board->black	= 0b1100'0000 * first_rank;
	board->pawn	= 0b0100'0010 * first_rank;
	board->rook	=  last_ranks * 0x0100'0000'0000'0001;
	board->knight	=  last_ranks * 0x0001'0000'0000'0100;
	board->bishop	=  last_ranks * 0x0000'0100'0001'0000;
	board->queen	=  last_ranks * 0x0000'0000'0100'0000;
	board->king	=  last_ranks * 0x0000'0001'0000'0000;
}

struct pieces {
	uint32_t nibble_file[8]; // every 4 bits represents a piece
};

static_assert(sizeof(struct board) == 8 * 8);
static_assert(sizeof(struct pieces) == 4 * 8);

void // follows the glyph layout in pieces_print
pieces_from_board(struct pieces *pieces, struct board *board) {
	memset(pieces->nibble_file, 0, sizeof(pieces->nibble_file));
	for (uint32_t piece = 0; piece != 6; ++piece) {
		for (uint64_t m = (&board->pawn)[piece]; m; m &= m - 1) {
			const unsigned i = __builtin_ctzg(m);
			uint32_t colored_piece = piece + 1;
			const bool black = board->black & 1 << i;
			if (black) colored_piece += 6;
			const unsigned file = i >> 3, rank = i & 07;
			pieces->nibble_file[file] |= colored_piece << (rank << 2);
		}
	}
}

void
pieces_print(struct pieces *pieces) {
	constexpr char glyph[13] = ".PRNBQKprnbqk";
	puts("    a b c d e f g h    ");
	puts("  +-----------------+  ");
	char line[] = "8 | r n b q k b n r | 8";
	unsigned shift = 32;
	do {
		shift -= 4;
		uint32_t *nibble_file = pieces->nibble_file;
		for (char *square = line + 4; *square != '|'; square += 2) {
			*square = glyph[*nibble_file++ >> shift & 0xf];
		}
		puts(line);
		--line[0];
		--line[22];
	} while (shift != 0);
	puts("  +-----------------+  ");
	puts("    a b c d e f g h    ");
}

int
main() {
	struct board board;
	board_init(&board);
	assert(board_invariant(&board));
	struct pieces pieces;
	pieces_from_board(&pieces, &board);
	pieces_print(&pieces);
	putchar('\n');
}
