#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>  

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
#endif

#define MATE 32000
#define MAX_PLY 64
#define KEYS_COUNT 896
#define U8 unsigned __int8
#define S16 signed __int16
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define FALSE 0
#define TRUE 1
#define NAME "Yeti"
#define VERSION "2026-05-22"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define FLIP(sq) ((sq)^0b111000)

enum Color { EMPTY = 0, WHITE = 8, BLACK = 16, COLOR_MASK = WHITE | BLACK, INVALID = 32 };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Piece {
	WHITE_PAWN = WHITE, WHITE_KNIGHT, WHITE_BISHOP, WHITE_ROOK, WHITE_QUEEN, WHITE_KING,
	BLACK_PAWN = BLACK, BLACK_KNIGHT, BLACK_BISHOP, BLACK_ROOK, BLACK_QUEEN, BLACK_KING
};
enum Castling { CWK = 1, CWQ = 2, CBK = 4, CBQ = 8 };
enum Bound { UPPER, LOWER, EXACT };
enum Squares {
	a8 = 21, b8, c8, d8, e8, f8, g8, h8,
	a7 = 31, b7, c7, d7, e7, f7, g7, h7,
	a6 = 41, b6, c6, d6, e6, f6, g6, h6,
	a5 = 51, b5, c5, d5, e5, f5, g5, h5,
	a4 = 61, b4, c4, d4, e4, f4, g4, h4,
	a3 = 71, b3, c3, d3, e3, f3, g3, h3,
	a2 = 81, b2, c2, d2, e2, f2, g2, h2,
	a1 = 91, b1, c1, d1, e1, f1, g1, h1, SQ_NB
};


typedef struct {
	U8 kingSq[2];
	U8 board[120];
	U8 color;
	U8 ep;
	U8 castle;
	U8 move50;
}Position;

Position pos;

typedef struct {
	U8 from;
	U8 to;
	U8 promo;
}Move;

typedef struct {
	Move move;
} Stack;

typedef struct {
	U64 hash;
	Move move;
	S16 score;
	U8 depth;
	U8 flag;
}TTEntry;

typedef struct {
	U8 post;
	U8 stop;
	U8 depthLimit;
	U64 timeStart;
	U64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}SearchInfo;

int historyCount = 0;
U64 historyHash[1024];
int dirOffset[16] = { 9, -9, -11, 11 ,1, -1, -10, 10, -21, -19, -12, -8, 8, 12, 19, 21 };
int dirStart[PT_NB] = { 0,8,0,4,0,0 };
int dirCount[PT_NB] = { 0,8,4,4,8,8 };
int dirSlide[PT_NB] = { 0,0,1,1,1,0 };
int phaseVal[PT_NB] = { 0,1,1,2,4,0 };
int insufVal[PT_NB] = { 3,1,2,3,3,0 };
U64 keys[KEYS_COUNT];
int mg_material[6] = { 82, 337, 365, 477, 1025, 0 };
int eg_material[6] = { 94, 281, 297, 512,  936, 0 };
int mx_material[6] = { 94, 337, 365, 477, 1025, 0 };
const U64 tt_count = 64ULL << 15;
int boardTo64[120];
TTEntry tt[64ULL << 15];
SearchInfo info;
Stack stack[MAX_PLY];

int boardCastle[64] = {
	 7, 15, 15, 15,  3, 15, 15, 11,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	13, 15, 15, 15, 12, 15, 15, 14
};

int mg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,  0,   0,
	 98, 134,  61,  95,  68, 126, 34, -11,
	 -6,   7,  26,  31,  65,  56, 25, -20,
	-14,  13,   6,  21,  23,  12, 17, -23,
	-27,  -2,  -5,  12,  17,   6, 10, -25,
	-26,  -4,  -4, -10,   3,   3, 33, -12,
	-35,  -1, -20, -23, -15,  24, 38, -22,
	  0,   0,   0,   0,   0,   0,  0,   0,
};

int eg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,   0,   0,
	178, 173, 158, 134, 147, 132, 165, 187,
	 94, 100,  85,  67,  56,  53,  82,  84,
	 32,  24,  13,   5,  -2,   4,  17,  17,
	 13,   9,  -3,  -7,  -7,  -8,   3,  -1,
	  4,   7,  -6,   1,   0,  -5,  -1,  -8,
	 13,   8,   8,  10,  13,   0,   2,  -7,
	  0,   0,   0,   0,   0,   0,   0,   0,
};

int mg_knight_table[64] = {
	-167, -89, -34, -49,  61, -97, -15, -107,
	 -73, -41,  72,  36,  23,  62,   7,  -17,
	 -47,  60,  37,  65,  84, 129,  73,   44,
	  -9,  17,  19,  53,  37,  69,  18,   22,
	 -13,   4,  16,  13,  28,  19,  21,   -8,
	 -23,  -9,  12,  10,  19,  17,  25,  -16,
	 -29, -53, -12,  -3,  -1,  18, -14,  -19,
	-105, -21, -58, -33, -17, -28, -19,  -23,
};

int eg_knight_table[64] = {
	-58, -38, -13, -28, -31, -27, -63, -99,
	-25,  -8, -25,  -2,  -9, -25, -24, -52,
	-24, -20,  10,   9,  -1,  -9, -19, -41,
	-17,   3,  22,  22,  22,  11,   8, -18,
	-18,  -6,  16,  25,  16,  17,   4, -18,
	-23,  -3,  -1,  15,  10,  -3, -20, -22,
	-42, -20, -10,  -5,  -2, -20, -23, -44,
	-29, -51, -23, -15, -22, -18, -50, -64,
};

int mg_bishop_table[64] = {
	-29,   4, -82, -37, -25, -42,   7,  -8,
	-26,  16, -18, -13,  30,  59,  18, -47,
	-16,  37,  43,  40,  35,  50,  37,  -2,
	 -4,   5,  19,  50,  37,  37,   7,  -2,
	 -6,  13,  13,  26,  34,  12,  10,   4,
	  0,  15,  15,  15,  14,  27,  18,  10,
	  4,  15,  16,   0,   7,  21,  33,   1,
	-33,  -3, -14, -21, -13, -12, -39, -21,
};

int eg_bishop_table[64] = {
	-14, -21, -11,  -8, -7,  -9, -17, -24,
	 -8,  -4,   7, -12, -3, -13,  -4, -14,
	  2,  -8,   0,  -1, -2,   6,   0,   4,
	 -3,   9,  12,   9, 14,  10,   3,   2,
	 -6,   3,  13,  19,  7,  10,  -3,  -9,
	-12,  -3,   8,  10, 13,   3,  -7, -15,
	-14, -18,  -7,  -1,  4,  -9, -15, -27,
	-23,  -9, -23,  -5, -9, -16,  -5, -17,
};

int mg_rook_table[64] = {
	 32,  42,  32,  51, 63,  9,  31,  43,
	 27,  32,  58,  62, 80, 67,  26,  44,
	 -5,  19,  26,  36, 17, 45,  61,  16,
	-24, -11,   7,  26, 24, 35,  -8, -20,
	-36, -26, -12,  -1,  9, -7,   6, -23,
	-45, -25, -16, -17,  3,  0,  -5, -33,
	-44, -16, -20,  -9, -1, 11,  -6, -71,
	-19, -13,   1,  17, 16,  7, -37, -26,
};

int eg_rook_table[64] = {
	13, 10, 18, 15, 12,  12,   8,   5,
	11, 13, 13, 11, -3,   3,   8,   3,
	 7,  7,  7,  5,  4,  -3,  -5,  -3,
	 4,  3, 13,  1,  2,   1,  -1,   2,
	 3,  5,  8,  4, -5,  -6,  -8, -11,
	-4,  0, -5, -1, -7, -12,  -8, -16,
	-6, -6,  0,  2, -9,  -9, -11,  -3,
	-9,  2,  3, -1, -5, -13,   4, -20,
};

int mg_queen_table[64] = {
	-28,   0,  29,  12,  59,  44,  43,  45,
	-24, -39,  -5,   1, -16,  57,  28,  54,
	-13, -17,   7,   8,  29,  56,  47,  57,
	-27, -27, -16, -16,  -1,  17,  -2,   1,
	 -9, -26,  -9, -10,  -2,  -4,   3,  -3,
	-14,   2, -11,  -2,  -5,   2,  14,   5,
	-35,  -8,  11,   2,   8,  15,  -3,   1,
	 -1, -18,  -9,  10, -15, -25, -31, -50,
};

int eg_queen_table[64] = {
	 -9,  22,  22,  27,  27,  19,  10,  20,
	-17,  20,  32,  41,  58,  25,  30,   0,
	-20,   6,   9,  49,  47,  35,  19,   9,
	  3,  22,  24,  45,  57,  40,  57,  36,
	-18,  28,  19,  47,  31,  34,  39,  23,
	-16, -27,  15,   6,   9,  17,  10,   5,
	-22, -23, -30, -16, -16, -23, -36, -32,
	-33, -28, -22, -43,  -5, -32, -20, -41,
};

int mg_king_table[64] = {
	-65,  23,  16, -15, -56, -34,   2,  13,
	 29,  -1, -20,  -7,  -8,  -4, -38, -29,
	 -9,  24,   2, -16, -20,   6,  22, -22,
	-17, -20, -12, -27, -30, -25, -14, -36,
	-49,  -1, -27, -39, -46, -44, -33, -51,
	-14, -14, -22, -46, -44, -30, -15, -27,
	  1,   7,  -8, -64, -43, -16,   9,   8,
	-15,  36,  12, -54,   8, -28,  24,  14,
};

int eg_king_table[64] = {
	-74, -35, -18, -18, -11,  15,   4, -17,
	-12,  17,  14,  17,  17,  38,  23,  11,
	 10,  17,  23,  15,  20,  45,  44,  13,
	 -8,  22,  24,  27,  26,  33,  26,   3,
	-18,  -4,  21,  24,  27,  23,   9, -11,
	-19,  -3,  11,  21,  23,  16,   7,  -9,
	-27, -11,   4,  13,  14,   4,  -5, -17,
	-53, -34, -21, -11, -28, -14, -24, -43
};

int* mg_table[6] = {
	mg_pawn_table,
	mg_knight_table,
	mg_bishop_table,
	mg_rook_table,
	mg_queen_table,
	mg_king_table
};

int* eg_table[6] = {
	eg_pawn_table,
	eg_knight_table,
	eg_bishop_table,
	eg_rook_table,
	eg_queen_table,
	eg_king_table
};

int mg_pst[16][64];
int eg_pst[16][64];
int mx_pst[16][64];

void UciCommand(char* line);

static inline int MakeSquare(int file, int rank) { return 21 + rank * 10 + file; }

static U64 Rand64() {
	static U64 next = 1;
	next = next * 12345104729 + 104723;
	return next;
}

static void Clear(Position* pos) {
	for (int x = 0; x < 10; x++)
		for (int y = 0; y < 12; y++)
			pos->board[x + y * 10] = x > 0 && x < 9 && y>1 && y < 10 ? EMPTY : INVALID;
}

static void Init() {
	for (int i = 0; i < KEYS_COUNT; ++i)
		keys[i] = Rand64();
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++)
			boardTo64[MakeSquare(x, y)] = y * 8 + x;
	for (int pt = PAWN; pt <= KING; pt++) {
		for (int sq = 0; sq < 64; sq++) {
			int mg = mg_material[pt] + mg_table[pt][sq];
			int eg = eg_material[pt] + eg_table[pt][sq];
			mg_pst[pt + WHITE][sq] = mg;
			mg_pst[pt][FLIP(sq)] = -mg;
			eg_pst[pt + WHITE][sq] = eg;
			eg_pst[pt][FLIP(sq)] = -eg;
			mx_pst[pt + WHITE][sq] = max(mg, eg);
			mx_pst[pt][FLIP(sq)] = max(mg, eg);
		}
	}
}

static inline U64 GetTimeMs() {
	return GetTickCount64();
}

static inline int MakePiece(int color, int pt) {
	return color | pt;
}

static inline int GetPieceColor(int piece) {
	return piece & COLOR_MASK;
}

static inline int GetPieceType(int piece) {
	if (piece == EMPTY)
		return PT_NB;
	return piece & 7;
}

static inline int FileOf(int sq) {
	return (sq-21) % 10;
}

static inline int RankOf(int sq) {
	return (sq-21) / 10;
}

static inline char CFileOf(int sq) {
	return 'a' + FileOf(sq);
}

static inline char CRankOf(int sq) {
	return '1' + (7 - RankOf(sq));
}

static int PieceTypeOnSquare(const Position* pos, int sq) {
	return GetPieceType(pos->board[sq]);
}

static int Distance(int sq1, int sq2) {
	int x1 = FileOf(sq1);
	int y1 = RankOf(sq1);
	int x2 = FileOf(sq2);
	int y2 = RankOf(sq2);
	return max(abs(x1 - x2), abs(y1 - y2));
}

static int InputAvailable(void) {
	static int init = 0, pipe;
	static HANDLE inh;
	DWORD dw;
	if (!init) {
		init = 1;
		inh = GetStdHandle(STD_INPUT_HANDLE);
		pipe = !GetConsoleMode(inh, &dw);
		if (!pipe) {
			SetConsoleMode(inh, dw & ~(ENABLE_MOUSE_INPUT | ENABLE_WINDOW_INPUT));
			FlushConsoleInputBuffer(inh);
		}
	}
	if (pipe) {
		if (!PeekNamedPipe(inh, NULL, 0, NULL, &dw, NULL))
			return 1;
		return dw > 0;
	}
	else {
		GetNumberOfConsoleInputEvents(inh, &dw);
		return dw > 1;
	}
}

static int CheckUp() {
	if ((++info.nodes & 0xffff) == 0) {
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit)
			info.stop = TRUE;
		if (info.nodesLimit && info.nodes > info.nodesLimit)
			info.stop = TRUE;
		if (InputAvailable()) {
			char line[4000];
			fgets(line, sizeof(line), stdin);
			UciCommand(line);
		}
	}
	return info.stop;
}

static char* ParseToken(char* string, char* token) {
	while (*string == ' ')
		string++;
	while (*string != ' ' && *string != '\0')
		*token++ = *string++;
	*token = '\0';
	return string;
}

static char* MoveToUci(Move move) {
	static char str[6] = { 0 };
	str[0] = CFileOf(move.from);
	str[1] = CRankOf(move.from);
	str[2] = CFileOf(move.to);
	str[3] = CRankOf(move.to);
	str[4] = "\0nbrq\0\0"[move.promo];
	return str;
}

static int StrToSquare(char* s) {
	int file = (s[0] - 'a');
	int rank = 7 - (s[1] - '1');
	return MakeSquare(file, rank);
}

static Move UciToMove(char* s) {
	Move m;
	m.from = StrToSquare(s);
	m.to = StrToSquare(s + 2);
	m.promo = PT_NB;
	switch (s[4]) {
	case 'N':
	case 'n':
		m.promo = KNIGHT;
		break;
	case 'B':
	case 'b':
		m.promo = BISHOP;
		break;
	case 'R':
	case 'r':
		m.promo = ROOK;
		break;
	case 'Q':
	case 'q':
		m.promo = QUEEN;
		break;
	}
	return m;
}

static U64 GetHash(const Position* pos) {
	U64 hash = pos->color;
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) {
			int sq = MakeSquare(x, y);
			int piece = pos->board[sq];
			if (piece)
				hash ^= keys[(piece & 0xf) * 64 + boardTo64[sq]];
		}
	if (pos->ep < SQ_NB)
		hash ^= keys[6 * 64 + boardTo64[pos->ep]];
	if (pos->castle)
		hash ^= keys[7 * 64 + pos->castle];
	return hash;
}

static int IsRepetition(Position* pos, U64 hash) {
	int limit = max(0, historyCount - pos->move50);
	for (int n = historyCount - 4; n >= limit; n -= 2)
		if (historyHash[n] == hash)
			return TRUE;
	return FALSE;
}

static int IsPseudolegalMove(const Position* pos, const Move move) {
	Move moves[256];
	const int inCheck = IsSquareAttacked(pos, pos->kingSq[pos->color == BLACK], pos->color ^ COLOR_MASK);
	const int num_moves = MoveGen(pos, moves, 0, inCheck);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i].from == move.from && moves[i].to == move.to)
			return 1;
	return 0;
}

static void PrintPv(const Position* pos, const Move move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	const Position npos = *pos;
	if (!MakeMove(&npos, &move))
		return;
	printf(" %s", MoveToUci(move));
	const U64 hash = GetHash(&npos);
	TTEntry* tt_entry = tt + (hash % tt_count);
	if (tt_entry->hash != hash || IsRepetition(pos, hash))
		return;
	historyHash[historyCount++] = hash;
	PrintPv(&npos, tt_entry->move);
	historyCount--;
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++)
		if (tt[n].hash)
			pm++;
	return pm;
}

static int EvalPosition(Position* pos) {
	int scoreMg = 0;
	int scoreEg = 0;
	int phase = 0;
	int insufficent[2] = { 0 };
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) {
			int sq = y * 8 + x;
			int piece = pos->board[MakeSquare(x, y)];
			if (piece == EMPTY)continue;
			int pt = GetPieceType(piece);
			int color = GetPieceColor(piece);
			int pc = piece & 0xf;
			phase += phaseVal[pt];
			insufficent[color == BLACK] += insufVal[pt];
			scoreMg += mg_pst[pc][sq];
			scoreEg += eg_pst[pc][sq];
		}
	if (max(insufficent[0], insufficent[1]) < 3)
		return 0;
	if (phase > 24) phase = 24;
	int score = (scoreMg * phase + scoreEg * (24 - phase)) / 24;
	score = (score * (100 - pos->move50)) / 100;
	return pos->color == WHITE ? score : -score;
}

static void SetFen(Position* pos, char* fen) {
	memset(pos, 0, sizeof(Position));
	Clear(pos);
	pos->ep = SQ_NB;
	int sq = 21;
	while (*fen && *fen != ' ') {
		switch (*fen) {
		case '1': sq += 1; break;
		case '2': sq += 2; break;
		case '3': sq += 3; break;
		case '4': sq += 4; break;
		case '5': sq += 5; break;
		case '6': sq += 6; break;
		case '7': sq += 7; break;
		case '8': sq += 8; break;
		case 'P': pos->board[sq++] = WHITE_PAWN; break;
		case 'N': pos->board[sq++] = WHITE_KNIGHT; break;
		case 'B': pos->board[sq++] = WHITE_BISHOP; break;
		case 'R': pos->board[sq++] = WHITE_ROOK; break;
		case 'Q': pos->board[sq++] = WHITE_QUEEN; break;
		case 'K': pos->kingSq[0] = sq; pos->board[sq++] = WHITE_KING; break;
		case 'p': pos->board[sq++] = BLACK_PAWN; break;
		case 'n': pos->board[sq++] = BLACK_KNIGHT; break;
		case 'b': pos->board[sq++] = BLACK_BISHOP; break;
		case 'r': pos->board[sq++] = BLACK_ROOK; break;
		case 'q': pos->board[sq++] = BLACK_QUEEN; break;
		case 'k': pos->kingSq[1] = sq; pos->board[sq++] = BLACK_KING; break;
		case '/': sq += 2; break;
		}
		fen++;
	}
	fen++;
	pos->color = *fen == 'w' ? WHITE : BLACK;
	while (*fen && *fen != ' ') fen++; fen++;
	while (*fen && *fen != ' ') {
		switch (*fen) {
		case 'K': pos->castle |= CWK; break;
		case 'Q': pos->castle |= CWQ; break;
		case 'k': pos->castle |= CBK; break;
		case 'q': pos->castle |= CBQ; break;
		case '-': break;
		}
		fen++;
	}
	fen++;
	if (*fen != '-')
		pos->ep = StrToSquare(fen);
	while (*fen && *fen != ' ') fen++; fen++;
	pos->move50 = atoi(fen);
}

static void AddMove(Move* const moveList, int* num_moves, const int from, const int to, const int promo) {
	Move* m = &moveList[(*num_moves)++];
	m->from = from;
	m->to = to;
	m->promo = promo;
}

static void AddPawnMove(Position* pos, Move* const moveList, int* num_moves, const int from, const int to, const int rank) {
	if (rank == 6) {
		for (int pt = KNIGHT; pt < KING; pt++)
			AddMove(moveList, num_moves, from, to, pt);
	}
	else
		AddMove(moveList, num_moves, from, to, PT_NB);
}

static int IsLegalMove(Position* pos, int sqFrom, int dir, int* sqTo) {
	*sqTo = sqFrom + dir;
	return pos->board[*sqTo] != INVALID;
}

static void GeneratePawnMoves(Position* pos, Move* const moveList, int* num_moves, int sqFrom, int dy, int onlyCaptures) {
	int sqTo = sqFrom + dy * 10;
	int rank = (pos->color == WHITE) ? (7 - RankOf(sqFrom)) : RankOf(sqFrom);
	int enColor = (pos->color == WHITE) ? BLACK : WHITE;
	if (!onlyCaptures && pos->board[sqTo] == EMPTY) {
		AddPawnMove(pos, moveList, num_moves, sqFrom, sqTo, rank);
		if (rank == 1) {
			int sqTo2 = sqFrom + dy * 20;
			if (pos->board[sqTo2] == EMPTY)
				AddMove(moveList, num_moves, sqFrom, sqTo2, PT_NB);
		}
	}
	int sq2 = sqTo + 1;
	if (pos->board[sq2] != INVALID)
		if ((GetPieceColor(pos->board[sq2]) == enColor) || (sq2 == pos->ep))
			AddPawnMove(pos, moveList, num_moves, sqFrom, sq2, rank);
	sq2 = sqTo - 1;
	if (pos->board[sq2] != INVALID)
		if ((GetPieceColor(pos->board[sq2]) == enColor) || (sq2 == pos->ep))
			AddPawnMove(pos, moveList, num_moves, sqFrom, sq2, rank);
}

static void GeneratePieceMoves(Position* pos, Move* const moveList, int* num_moves, const int sqFrom, const int dir, int slider, int onlyCaptures) {
	int sq;
	int del = dir;
	if (slider > 1)
		del = dir * slider;
	if (IsLegalMove(pos,sqFrom, del, &sq)) {
		int piece = pos->board[sq];
		if (GetPieceColor(piece) == pos->color)
			return;
		if (piece || !onlyCaptures)
			AddMove(moveList, num_moves, sqFrom, sq, PT_NB);
		if (piece)
			return;
		if (slider)
			GeneratePieceMoves(pos, moveList, num_moves, sqFrom, dir, ++slider, onlyCaptures);
	}
}

static int MoveGen(Position* pos, Move* const moveList, int onlyCaptures, int inCheck) {
	int num_moves = 0;
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) {
			int sq = MakeSquare(x, y);
			int piece = pos->board[sq];
			if ((piece & COLOR_MASK) != pos->color)
				continue;
			int pt = GetPieceType(piece);
			int start = dirStart[pt];
			for (int n = 0; n < dirCount[pt]; n++)
				GeneratePieceMoves(pos, moveList, &num_moves, sq, dirOffset[start + n], dirSlide[pt], onlyCaptures);
			switch (piece) {
			case WHITE_PAWN:
				GeneratePawnMoves(pos, moveList, &num_moves, sq, -1, onlyCaptures);
				break;
			case BLACK_PAWN:
				GeneratePawnMoves(pos, moveList, &num_moves, sq, 1, onlyCaptures);
				break;
			case WHITE_KING:
				if (!onlyCaptures && !inCheck) {
					if (pos->castle & CWK)
						if (pos->board[f1] == EMPTY && pos->board[g1] == EMPTY && !IsSquareAttacked(pos, f1, BLACK))
							AddMove(moveList, &num_moves, e1, g1, PT_NB);
					if (pos->castle & CWQ)
						if (pos->board[d1] == EMPTY && pos->board[b1] == EMPTY && pos->board[c1] == EMPTY && !IsSquareAttacked(pos, d1, BLACK))
							AddMove(moveList, &num_moves, e1, c1, PT_NB);
				}
				break;
			case BLACK_KING:
				if (!onlyCaptures && !inCheck) {
					if (pos->castle & CBK)
						if (pos->board[f8] == EMPTY && pos->board[g8] == EMPTY && !IsSquareAttacked(pos, f8, WHITE))
							AddMove(moveList, &num_moves, e8, g8, PT_NB);
					if (pos->castle & CBQ)
						if (pos->board[d8] == EMPTY && pos->board[b8] == EMPTY && pos->board[c8] == EMPTY && !IsSquareAttacked(pos, d8, WHITE))
							AddMove(moveList, &num_moves, e8, c8, PT_NB);
				}
				break;
			}//case
		}
	return num_moves;
}

static void PrintBoard(Position* pos) {
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	printf(t);
	for (int rank = 0; rank < 8; rank++) {
		printf(s);
		printf(" %d |", 8 - rank);
		for (int file = 0; file < 8; file++) {
			int sq = MakeSquare(file, rank);
			int piece = pos->board[sq];
			int pt = GetPieceType(piece);
			int color = GetPieceColor(piece);
			if (color == WHITE)
				printf(" %c |", "ANBRQK "[pt]);
			else if (color == BLACK)
				printf(" %c |", "anbrqk "[pt]);
			else
				printf("   |");
		}
		printf(" %d \n", 8 - rank);
	}
	printf(s);
	printf(t);
	char castling[5] = "KQkq";
	for (int n = 0; n < 4; n++)
		if (!(pos->castle & 1 << n))
			castling[n] = '-';
	printf("side     : %16s\n", pos->color == WHITE ? "white" : "black");
	printf("castling : %16s\n", castling);
	printf("hash     : %16llx\n", GetHash(pos));
}

static void PrintInfo(Position* pos, int depth, int score) {
	printf("info depth %d score ", depth);
	if (abs(score) < MATE - MAX_PLY)
		printf("cp %d", score);
	else
		printf("mate %d", (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1));
	printf(" time %lld", GetTimeMs() - info.timeStart);
	printf(" nodes %lld", info.nodes);
	printf(" hashfull %d pv", Permill());
	PrintPv(pos, stack[0].move);
	printf("\n");
}

static int EvalMove(Position* pos, Move* bst, Move* m) {
	int pSou = pos->board[m->from];
	int pDes = pos->board[m->to];
	int ptSou = GetPieceType(pSou);
	int ptDes = GetPieceType(pDes);
	int pc = pSou & 0xf;
	int score = mx_pst[pc][boardTo64[m->to]] - mx_pst[pc][boardTo64[m->from]];
	if ((m->from == bst->from) && (m->to == bst->to))
		score += 10000;
	if (m->promo < PT_NB)
		score += mx_material[m->promo] - mx_material[PAWN];
	if (pDes)
		score += mx_material[ptDes] - mx_material[ptSou] / 10;
	return score;
}

static Move PickMove(Position* pos, Move* moveList, int* scoreList, int num_moves, int from) {
	int bestIndex = from;
	int bestScore = scoreList[from];
	Move m = moveList[from];
	for (int i = from + 1; i < num_moves; i++) {
		if (bestScore < scoreList[i]) {
			bestIndex = i;
			bestScore = scoreList[i];
			m = moveList[i];
		}
	}
	moveList[bestIndex] = moveList[from];
	scoreList[bestIndex] = scoreList[from];
	return m;
}

static int SearchAlpha(Position* pos, int alpha, int beta, int depth, int ply) {
	if (CheckUp())
		return 0;
	int  mate_value = MATE - ply;
	if (alpha < -mate_value)
		alpha = -mate_value;
	if (beta > mate_value - 1)
		beta = mate_value - 1;
	if (alpha >= beta)
		return alpha;
	const int static_eval = EvalPosition(pos);
	if (ply >= MAX_PLY)
		return static_eval;
	const int inCheck = IsSquareAttacked(pos, pos->kingSq[pos->color == BLACK], pos->color ^ COLOR_MASK);
	if (inCheck)
		depth = max(1, depth + 1);
	int inQuiescence = depth < 1;
	if (inQuiescence&& alpha < static_eval) {
		alpha = static_eval;
		if (alpha >= beta)
			return beta;
	}
	const U64 hash = GetHash(pos);
	if (ply && !inQuiescence)
		if (pos->move50 >= 100 || IsRepetition(pos, hash))
			return 0;
	TTEntry* tt_entry = tt + (hash % tt_count);
	Move tt_move = { 0 };
	int inPv = beta - alpha > 1;
	if (tt_entry->hash == hash) {
		tt_move = tt_entry->move;
		if (!inPv && tt_entry->depth >= depth) {
			if (tt_entry->flag == EXACT)return tt_entry->score;
			if (tt_entry->flag == LOWER && tt_entry->score <= alpha)return tt_entry->score;
			if (tt_entry->flag == UPPER && tt_entry->score >= beta)return tt_entry->score;
		}
	}
	else
		depth -= depth > 3;
	historyHash[historyCount++] = hash;
	U8 tt_flag = LOWER;
	int legalMoves = 0;
	int score;
	Move moves[256];
	int scoreList[256];
	const int num_moves = MoveGen(pos, moves, inQuiescence, inCheck);
	for (int n = 0; n < num_moves; n++)
		scoreList[n] = EvalMove(pos, &tt_move, &moves[n]);
	for (int n = 0; n < num_moves; n++) {
		Move move = PickMove(pos, moves, scoreList, num_moves, n);
		Position npos = *pos;
		if (!MakeMove(&npos, &move))
			continue;
		if (!legalMoves || depth < 4)
			score = -SearchAlpha(&npos, -beta, -alpha, depth - 1, ply + 1);
		else {
			int r = !inPv;
			score = -SearchAlpha(&npos, -alpha - 1, -alpha, depth - 1 - r, ply + 1);
			if (BLACK_ROOK && score > alpha)
				score = -SearchAlpha(&npos, -alpha - 1, -alpha, depth - 1, ply + 1);
			if (score > alpha && score < beta)
				score = -SearchAlpha(&npos, -beta, -alpha, depth - 1, ply + 1);
		}
		legalMoves++;
		if (info.stop)
			break;
		if (alpha < score) {
			alpha = score;
			stack[ply].move = move;
			tt_flag = EXACT;
			if (!ply && info.post)
				PrintInfo(pos, depth, score);
			if (alpha >= beta) {
				tt_flag = UPPER;
				break;
			}
		}
	}
	historyCount--;
	if (!legalMoves && !inQuiescence)
		return inCheck ? ply - MATE : 0;
	tt_entry->hash = hash;
	tt_entry->move = stack[ply].move;
	tt_entry->depth = max(0, depth);
	tt_entry->score = alpha;
	tt_entry->flag = tt_flag;
	return alpha;
}

static void SearchIteratively(Position* pos) {
	memset(tt, 0, sizeof(tt));
	int score = 0;
	int alpha = -MATE;
	int beta = MATE;
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		int aspH = 16, aspL = 16;
		do {
			if (depth > 4) {
				alpha = score - aspL;
				beta = score + aspH;
			}
			score = SearchAlpha(pos, alpha, beta, depth, 0);
			if (score <= alpha) {
				alpha -= aspL;
				aspL *= 2;
			}
			else if (score >= beta) {
				beta += aspH;
				aspH *= 2;
			}
			else
				break;
		} while (!info.stop);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2)
			break;
	}
	char* uci = MoveToUci(stack[0].move);
	if (info.post)
		printf("bestmove %s\n", uci);
	fflush(stdout);
}

static int GetSliderPiece(Position* pos, int sqFrom, int dir) {
	int sqTo;
	if (IsLegalMove(pos,sqFrom, dir, &sqTo)) {
		if (pos->board[sqTo] != EMPTY)
			return pos->board[sqTo];
		return GetSliderPiece(pos, sqTo, dir);
	}
	return EMPTY;
}

static int IsSquareAttacked(Position* pos, int sq, int byColor) {
	int sq2;
	int dy = byColor == WHITE ? 1 : -1;
	for (int dx = -1; dx <= 1; dx += 2)
		if (IsLegalMove(pos,sq, dy * 10 + dx, &sq2) && (pos->board[sq2] == MakePiece(byColor, PAWN)))
			return TRUE;
	for (int n = 0; n < 8; n++)
		if (IsLegalMove(pos,sq, dirOffset[8 + n], &sq2) && (pos->board[sq2] == MakePiece(byColor, KNIGHT)))
			return TRUE;
	int c = byColor == BLACK;
	if (Distance(sq, pos->kingSq[c]) == 1)
		return TRUE;
	int bishop = MakePiece(byColor, BISHOP);
	int rook = MakePiece(byColor, ROOK);
	int queen = MakePiece(byColor, QUEEN);
	for (int n = 0; n < 4; n++) {
		int piece = GetSliderPiece(pos, sq, dirOffset[n]);
		if ((piece == bishop) || (piece == queen))
			return TRUE;
		piece = GetSliderPiece(pos, sq, dirOffset[n + 4]);
		if ((piece == rook) || (piece == queen))
			return TRUE;
	}
	return FALSE;
}

static void MovePiece(Position* pos, int from, int to) {
	pos->board[to] = pos->board[from];
	pos->board[from] = EMPTY;
}

static int MakeMove(Position* pos, const Move* move) {
	int ep = pos->ep;
	pos->ep = SQ_NB;
	if (pos->board[move->to])
		pos->move50 = 0;
	else
		pos->move50++;
	int piece = pos->board[move->from];
	if (piece == WHITE_KING) {
		pos->kingSq[0] = move->to;
		if (move->from == e1) {
			if (move->to == g1)
				MovePiece(pos, h1, f1);
			else if (move->to == c1)
				MovePiece(pos, a1, d1);
		}
	}
	else if (piece == BLACK_KING) {
		pos->kingSq[1] = move->to;
		if (move->from == e8) {
			if (move->to == g8)
				MovePiece(pos, h8, f8);
			else if (move->to == c8)
				MovePiece(pos, a8, d8);
		}
	}
	int pt = GetPieceType(piece);
	if (pt == PAWN) {
		if (move->to == ep)
			if (pos->color == WHITE)
				pos->board[move->to + 10] = EMPTY;
			else
				pos->board[move->to - 10] = EMPTY;
		if (abs(move->from - move->to) == 20)
			pos->ep = (move->from + move->to) / 2;
		pos->move50 = 0;
	}
	MovePiece(pos, move->from, move->to);
	if (move->promo < PT_NB)
		pos->board[move->to] = MakePiece(pos->color, move->promo);
	pos->castle &= boardCastle[boardTo64[move->from]] & boardCastle[boardTo64[move->to]];
	pos->color ^= COLOR_MASK;
	return !IsSquareAttacked(pos, pos->kingSq[pos->color == WHITE], pos->color);
}

static int ShrinkNumber(U64 n) {
	if (n < 10000)
		return 0;
	if (n < 10000000)
		return 1;
	if (n < 10000000000)
		return 2;
	return 3;
}

static void PrintSummary(U64 time, U64 nodes) {
	U64 nps = (nodes * 1000) / max(time, 1);
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	int p = pow(10, sn * 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

static void ResetInfo() {
	info.timeStart = GetTimeMs();
	info.timeLimit = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.nodes = 0;
	info.stop = FALSE;
	info.post = TRUE;
}

static inline void PerftDriver(Position* pos, int depth) {
	Move moves[256];
	const int inCheck = IsSquareAttacked(pos, pos->kingSq[pos->color == BLACK], pos->color ^ COLOR_MASK);
	const int num_moves = MoveGen(pos, moves, 0, inCheck);
	for (int n = 0; n < num_moves; n++) {
		Position npos = *pos;
		if (!MakeMove(&npos, &moves[n]))
			continue;
		if (depth)
			PerftDriver(&npos, depth - 1);
		else
			info.nodes++;
	}
}

//performance test
static inline void UciPerformance(Position* pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		PerftDriver(pos, info.depthLimit++);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

//start benchmark
static void UciBench(Position* pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	info.post = FALSE;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		++info.depthLimit;
		SearchIteratively(pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

static void ParsePosition(char* ptr) {
	char token[80], fen[80];
	ptr = ParseToken(ptr, token);
	if (strcmp(token, "fen") == 0) {
		fen[0] = '\0';
		while (1) {
			ptr = ParseToken(ptr, token);
			if (*token == '\0' || strcmp(token, "moves") == 0)
				break;
			strcat(fen, token);
			strcat(fen, " ");
		}
		SetFen(&pos, fen);
	}
	else {
		ptr = ParseToken(ptr, token);
		SetFen(&pos, START_FEN);
	}
	historyCount = 0;
	if (strcmp(token, "moves") == 0)
		while (1) {
			ptr = ParseToken(ptr, token);
			if (*token == '\0')
				break;
			Move m = UciToMove(token);
			if (PieceTypeOnSquare(&pos, m.to) != PT_NB || PieceTypeOnSquare(&pos, m.from) == PAWN)
				historyCount = 0;
			historyHash[historyCount++] = GetHash(&pos);
			MakeMove(&pos, &m);
		}
}

static void ParseGo(char* command) {
	ResetInfo();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	char* argument = NULL;
	if (argument = strstr(command, "binc"))
		binc = atoi(argument + 5);
	if (argument = strstr(command, "winc"))
		winc = atoi(argument + 5);
	if (argument = strstr(command, "wtime"))
		wtime = atoi(argument + 6);
	if (argument = strstr(command, "btime"))
		btime = atoi(argument + 6);
	if ((argument = strstr(command, "movestogo")))
		movestogo = atoi(argument + 10);
	if ((argument = strstr(command, "movetime")))
		info.timeLimit = atoi(argument + 9);
	if ((argument = strstr(command, "depth")))
		info.depthLimit = atoi(argument + 6);
	if (argument = strstr(command, "nodes"))
		info.nodesLimit = atoi(argument + 5);
	int time = pos.color == WHITE ? wtime : btime;
	int inc = pos.color == WHITE ? winc : binc;
	if (time)
		info.timeLimit = min(time / movestogo + inc, time / 2);
	SearchIteratively(&pos);
}

void UciCommand(char* line) {
	if (strncmp(line, "ucinewgame", 10) == 0)
		memset(tt, 0, sizeof(tt));
	else if (!strncmp(line, "uci", 3)) {
		printf("id name %s\nuciok\n", NAME);
		fflush(stdout);
	}
	else if (!strncmp(line, "isready", 7)) {
		printf("readyok\n");
		fflush(stdout);
	}
	else if (!strncmp(line, "go", 2))
		ParseGo(line + 2);
	else if (!strncmp(line, "position", 8))
		ParsePosition(line + 8);
	else if (!strncmp(line, "print", 5))
		PrintBoard(&pos);
	else if (!strncmp(line, "perft", 5))
		UciPerformance(&pos);
	else if (!strncmp(line, "bench", 5))
		UciBench(&pos);
	else if (!strncmp(line, "stop", 4))
		info.stop = TRUE;
	else if (!strncmp(line, "quit", 4))
		exit(0);
}

static void UciLoop() {
	char line[4000];
	while (fgets(line, sizeof(line), stdin))
		UciCommand(line);
}

int main(const int argc, const char** argv) {
	Init();
	printf("%s %s\n", NAME, VERSION);
	SetFen(&pos, START_FEN);
	UciLoop();
}
