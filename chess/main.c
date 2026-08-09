/*******************************************************************************

- https://en.wikipedia.org/wiki/Chess
- https://www.overleaf.com/learn/latex/Chess_notation

## Forsyth-Edwards Notation (FEN)
- White pieces are identified by uppercase letters (PNBRQK).
- Black pieces are identified by lowercase letters (pnbrqk).

*******************************************************************************/

#include <stdio.h>

int main() {
	puts(
		"    a b c d e f g h    \n"
		"  +-----------------+  \n"
		"8 | r n b q k b n r | 8\n"
		"7 | p p p p p p p p | 7\n"
		"6 | . . . . . . . . | 6\n"
		"5 | . . . . . . . . | 5\n"
		"4 | . . . . . . . . | 4\n"
		"3 | . . . . . . . . | 3\n"
		"2 | P P P P P P P P | 2\n"
		"1 | R N B Q K B N R | 1\n"
		"  +-----------------+  \n"
		"    a b c d e f g h    \n"
	);
}
