#include <iostream>
#include <sstream>
#include <random>

using namespace std;

#define U64 unsigned __int64
#define U32 unsigned __int32
#define U16 unsigned __int16
#define U8  unsigned __int8
#define S64 signed __int64
#define S32 signed __int32
#define S16 signed __int16
#define S8  signed __int8
#define MAX_PLY 64
#define INF 32001
#define MATE 32000
#define NAME "Yeti"
#define VERSION "2025-10-22"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define FLIP(sq) ((sq)^56)

enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { LOWER, UPPER, EXACT };

struct Stack {
	int move;
};

struct SearchInfo {
	bool stop;
	bool post;
	U8 depthLimit;
	S64 timeStart;
	S64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}info;

struct TTEntry {
	U64 hash;
	short score, move;
	char  depth, flag;
};

const int HASH_SIZE = 64ULL << 15;
const int INVALID = 32, EMPTY = 0, WHITE = 8, BLACK = 16;
const int W_KS = 1, W_QS = 2, B_KS = 4, B_QS = 8;
const int P_dirs[8] = { -10, -20, -9, -11, 10, 20, 9, 11 };
const int N_dirs[8] = { -21, -19, -12, -8, 8, 12, 19, 21 };
const int B_dirs[4] = { 9, -9, -11, 11 };
const int R_dirs[4] = { 1, -1,  -10, 10 };
const int Q_dirs[8] = { 1, -1, 9, -9, 10, -10, 11, -11 };
int inline static Src(int move) { return (move & 0x7f); }
int inline static Dst(int move) { return ((move >> 7) & 0x7f); }
int inline static Promo(int move) { return ((move >> 14) & 7); }
int inline static Value(int move) { return ((move >> 17) & 0x3fff); }
int inline static Switch(int color) { return color ^ (WHITE | BLACK); }
int inline static File(int sq) { return sq % 10; }
int inline static Rank(int sq) { return sq / 10 - 1; }
int inline static Sq(int file, int rank) { return 21 + file + rank * 10; }
int inline static RelativeRank(int sq, int col) { return col == BLACK ? (sq - 10) / 10 : 9 - (sq - 10) / 10; }
int hash_count = 0;
U64 hash_history[2000];
U64 keys[128 * 16];
int SetCastle[120];
int board64[120];
const int KingEval[10] = { 0, 8, 12, 5, 0, 0, 5, 14, 9, 0 };
const int CentEval[10] = { 0,-6, -3, -1, 0, 0, -1, -3, -6, 0 };
const int PawnEval[10] = { 0, 1, 2, 2, 3, 3, 2, 1, 1, 0 };
Stack stack[MAX_PLY]{};
TTEntry tt[HASH_SIZE]{};

int mg_value[PT_NB] = { 82, 337, 365, 477, 1025, 0 };
int eg_value[PT_NB] = { 94, 281, 297, 512,  936, 0 };
int mm_value[PT_NB] = { 94, 337, 365, 477, 1025, 0 };

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
int mm_pst[16][64];

static int MakePiece(int color, int pt) {
	return color | pt;
}

static int TypeOf(int piece) {
	return piece & 7;
}

static void InitEval() {
	for (int pt = PAWN; pt <= KING; pt++) {
		for (int sq = 0; sq < 64; sq++) {
			int file = sq % 8;
			int rank = sq / 8;
			board64[Sq(file, rank)] = sq;
			int pcw = MakePiece(WHITE, pt) & 0xf;
			int pcb = MakePiece(BLACK, pt) & 0xf;
			int mg = mg_value[pt] + mg_table[pt][sq];
			int eg = eg_value[pt] + eg_table[pt][sq];
			mg_pst[pcw][sq] = mg;
			mg_pst[pcb][FLIP(sq)] = -mg;
			eg_pst[pcw][sq] = eg;
			eg_pst[pcb][FLIP(sq)] = -eg;
			mm_pst[pcw][sq] = max(mg, eg);
			mm_pst[pcb][FLIP(sq)] = max(mg, eg);
		}
	}
}

static string SquareToUci(const int sq) {
	string str;
	int r = 8 - Rank(sq);
	int f = File(sq) - 1;
	str += 'a' + f;
	str += '1' + r;
	return str;
}

static string MoveToUci(int move) {
	int src = Src(move);
	int dst = Dst(move);
	int promo = Promo(move);
	string uci = SquareToUci(src) + SquareToUci(dst);
	if (promo < KING)
		uci += "pnbrqk"[promo];
	return uci;
}

static int UciToMove(string s) {
	int Src = Sq(s[0] - 'a', 7 - (s[1] - '1'));
	int Dst = Sq(s[2] - 'a', 7 - (s[3] - '1'));
	int Upgrade = PT_NB;
	if (s[4] == 'n' || s[4] == 'N') Upgrade = KNIGHT;
	if (s[4] == 'b' || s[4] == 'B') Upgrade = BISHOP;
	if (s[4] == 'r' || s[4] == 'R') Upgrade = ROOK;
	if (s[4] == 'q' || s[4] == 'R') Upgrade = QUEEN;
	return Src + (Dst << 7) + (Upgrade << 14);
}

static void TTClear() {
	std::memset(tt, 0, sizeof(TTEntry) * HASH_SIZE);
}

struct Position {
	unsigned char board[120];
	int move50, color, EPsq, castling, WKsq, BKsq, phaseW, phaseB;

	void Clear() {
		move50 = color = EPsq = WKsq = BKsq = phaseW = phaseB = 0;
		castling = 0xf;
		for (int x = 0; x < 10; x++)
			for (int y = 0; y < 12; y++)
				board[x + y * 10] = x > 0 && x < 9 && y>1 && y < 10 ? EMPTY : INVALID;
	}

	int Evaluate() {
		int phases[PT_NB] = { 0,1,1,2,4,0 };
		int mg = 0, eg = 0;
		for (int y = 0; y < 8; y++)
			for (int x = 0; x < 8; x++) {
				int sq = y * 8 + x;
				int piece = board[Sq(x, y)];
				if (piece == EMPTY) continue;
				int pt = piece & 7;
				int pc = piece & 0xf;
				if (piece & WHITE)
					phaseW += phases[pt];
				else
					phaseB += phases[pt];
				mg += mg_pst[pc][sq];
				eg += eg_pst[pc][sq];
			}
		int phase = phaseW + phaseB;
		if (phase > 24) phase = 24;
		return (mg * phase + eg * (24 - phase)) / 24;
	}

	void Init() {
		int sq, pc;
		Clear();
		for (sq = 0; sq < 120; sq++)
			SetCastle[sq] = 0;
		SetCastle[21] = B_QS; SetCastle[28] = B_KS; SetCastle[25] = B_QS | B_KS;
		SetCastle[91] = W_QS; SetCastle[98] = W_KS; SetCastle[95] = W_QS | W_KS;
	}

	void PutPiece(int sq, PieceType pt, int color) {
		board[sq] = MakePiece(color, pt);
		if (pt == KING)
			if (color == WHITE)
				WKsq = sq;
			else
				BKsq = sq;
	}

	void SetFen(string fen) {
		Clear();
		int sq = 21;
		stringstream ss(fen);
		string token;
		ss >> token;
		for (char c : token)
			switch (c) {
			case 'p':PutPiece(sq++, PAWN, BLACK); break;
			case 'n':PutPiece(sq++, KNIGHT, BLACK); break;
			case 'b':PutPiece(sq++, BISHOP, BLACK); break;
			case 'r':PutPiece(sq++, ROOK, BLACK); break;
			case 'q':PutPiece(sq++, QUEEN, BLACK); break;
			case 'k':PutPiece(sq++, KING, BLACK); break;
			case 'P':PutPiece(sq++, PAWN, WHITE); break;
			case 'N':PutPiece(sq++, KNIGHT, WHITE); break;
			case 'B':PutPiece(sq++, BISHOP, WHITE); break;
			case 'R':PutPiece(sq++, ROOK, WHITE); break;
			case 'Q':PutPiece(sq++, QUEEN, WHITE); break;
			case 'K':PutPiece(sq++, KING, WHITE); break;
			case '1': sq += 1; break;
			case '2': sq += 2; break;
			case '3': sq += 3; break;
			case '4': sq += 4; break;
			case '5': sq += 5; break;
			case '6': sq += 6; break;
			case '7': sq += 7; break;
			case '8': sq += 8; break;
			case '/': sq += 2; break;
			}

		ss >> token;
		color = (token == "w") ? WHITE : BLACK;

		ss >> token;
		for (char c : token)
			switch (c) {
			case 'K':
				castling ^= W_KS;
				break;
			case 'Q':
				castling ^= W_QS;
				break;
			case 'k':
				castling ^= B_KS;
				break;
			case 'q':
				castling ^= B_QS;
				break;
			}

		ss >> token;
		if (token != "-") {
			int file = token[0] - 'a';
			int rank = 7 - (token[1] - '1');
			EPsq = Sq(file, rank);
		}
		ss >> token;
		move50 = stoi(token);
	}

	int CanCastleKS(const int Color) const {
		if (Color == WHITE && !(castling & W_KS) && board[WKsq + 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq + 1) && board[WKsq + 2] == EMPTY) return 1;
		if (Color == BLACK && !(castling & B_KS) && board[BKsq + 1] == EMPTY && !ColorAttacksSq(WHITE, BKsq + 1) && board[BKsq + 2] == EMPTY) return 1;
		return 0;
	}

	int CanCastleQS(const int Color) const {
		if (Color == WHITE && !(castling & W_QS) && board[WKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq - 1) && board[WKsq - 2] == EMPTY && board[WKsq - 3] == EMPTY) return 1;
		if (Color == BLACK && !(castling & B_QS) && board[BKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, BKsq - 1) && board[BKsq - 2] == EMPTY && board[BKsq - 3] == EMPTY) return 1;
		return 0;
	}

	void MovePiece(const int Src, const int Dst, const int promo) {
		int piece = board[Src];
		if (board[Dst] != EMPTY)
			move50 = 0;
		board[Dst] = piece;
		board[Src] = EMPTY;
		if (piece == (KING | WHITE)) WKsq = Dst;
		if (piece == (KING | BLACK)) BKsq = Dst;
		if ((piece & 7) == PAWN) {
			move50 = 0;
			if (Dst < 30 || Dst > 90)
				board[Dst] += promo;
			if (Dst == EPsq) {
				EPsq = Src + File(Dst) - File(Src);
				board[EPsq] = EMPTY;
			}
			if (abs(Src - Dst) == 20)
				EPsq = ((Src + Dst) >> 1);
			else EPsq = 0;
		}
		else EPsq = 0;
	}

	void DoMove(const int Move) {
		move50++;
		int dst = Dst(Move), src = Src(Move);
		castling |= SetCastle[src] | SetCastle[dst];
		color = Switch(color);
		if ((board[src] & 7) == KING) {
			if (dst == src - 2)
				MovePiece(src - 4, src - 1, 0);
			if (dst == src + 2)
				MovePiece(src + 3, src + 1, 0);
		}
		MovePiece(src, dst, Promo(Move));
	}

	int CheckDirec(int Sq, const int Dir, const int Piece1, const int Piece2) const {
		Sq += Dir;
		while (board[Sq] == EMPTY) Sq += Dir;
		if (board[Sq] == Piece1 || board[Sq] == Piece2) return 1; else	return 0;
	}

	int ColorAttacksSq(int Color, int Sq) const {
		int i;
		for (i = 0; i < 8; i++)
			if (board[Sq + N_dirs[i]] == (KNIGHT | Color))
				return 1;
		for (i = 0; i < 8; i++)
			if (board[Sq + Q_dirs[i]] == (KING | Color))
				return 1;
		for (i = 0; i < 4; i++)
			if (CheckDirec(Sq, R_dirs[i], (QUEEN | Color), (ROOK | Color)))
				return 1;
		for (i = 0; i < 4; i++)
			if (CheckDirec(Sq, B_dirs[i], (QUEEN | Color), (BISHOP | Color)))
				return 1;
		int n = (Color == WHITE) ? 4 : 0;
		for (i = 2; i <= 3; i++)
			if (board[Sq + P_dirs[i + n]] == (PAWN | Color))
				return 1;
		return 0;
	}

	int IsCheck(int color) const {
		return (color == WHITE) ? ColorAttacksSq(BLACK, WKsq) : ColorAttacksSq(WHITE, BKsq);
	}

	U64 GetHash() {
		U64 CheckSum = color;
		for (int index = 21; index <= 99; index++) {
			int nPiece = board[index];
			if (nPiece == INVALID) continue;
			if (nPiece == EMPTY) continue;
			CheckSum ^= keys[index << 4 | (nPiece & 0xf)];
		}
		return CheckSum;
	}

}pos;

struct Movelist
{
	int m_Moves[256];
	int count, m_onlyCapture;
	unsigned char* m_board = NULL;

	void inline AddMove(int Src, int Dst, bool promo = false) {
		if (promo)
			AddPromoMove(Src, Dst);
		else if (!m_onlyCapture)
			m_Moves[count++] = Src + (Dst << 7) + (PT_NB << 14) + (200 << 17);
	}

	void inline AddAtkMove(int Src, int Dst, bool promo = false) {
		if (promo)
			AddPromoMove(Src, Dst);
		else
			m_Moves[count++] = Src + (Dst << 7) + (PT_NB << 14) + ((200 + mm_value[(m_board[Dst] & 7)]) << 17);
	}

	void inline AddPromoMove(int Src, int Dst) {
		m_Moves[count++] = Src + (Dst << 7) + (KNIGHT << 14) + ((mm_value[KNIGHT]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (BISHOP << 14) + ((mm_value[BISHOP]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (ROOK << 14) + ((mm_value[ROOK]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (QUEEN << 14) + ((mm_value[QUEEN]) << 17);
	}

	void inline GenPieceMoves(const int MoveArray[], const int bSlide, const int nDirs, int Sq, Position& Board, const int COLOR) {
		for (int i = 0; i < nDirs; i++) {
			int tempSq = Sq + MoveArray[i];
			if (bSlide)
				while (Board.board[tempSq] == EMPTY) {
					AddMove(Sq, tempSq);
					tempSq += MoveArray[i];
				}
			if (Board.board[tempSq] & Switch(COLOR))
				AddAtkMove(Sq, tempSq);
			else if (Board.board[tempSq] == EMPTY)
				AddMove(Sq, tempSq);
		}
	}

	void inline GenPawnMoves(const int MoveArray[], int Sq, Position& Board, const int COLOR) {
		int n = (COLOR == BLACK) ? 4 : 0;
		int rank = RelativeRank(Sq, COLOR);
		if (Board.board[Sq + P_dirs[n]] == EMPTY) {
			AddMove(Sq, Sq + P_dirs[n], rank == 7);
			if (rank == 2 && Board.board[Sq + P_dirs[n + 1]] == EMPTY)
				AddMove(Sq, Sq + P_dirs[n + 1]);
		}
		if (Sq + P_dirs[n + 2] == Board.EPsq || (Board.board[Sq + P_dirs[n + 2]] & Switch(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 2], rank == 7);
		if (Sq + P_dirs[n + 3] == Board.EPsq || (Board.board[Sq + P_dirs[n + 3]] & Switch(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 3], rank == 7);
	}

	void Generate(Position& pos, int onlyCapture) {
		count = 0;
		m_onlyCapture = onlyCapture;
		m_board = pos.board;
		int color = pos.color;
		for (int sq = 20; sq < 100; sq++)
			switch (pos.board[sq] ^ color) {
			case PAWN: GenPawnMoves(P_dirs, sq, pos, color); break;
			case KNIGHT: GenPieceMoves(N_dirs, 0, 8, sq, pos, color); break;
			case BISHOP: GenPieceMoves(B_dirs, 1, 4, sq, pos, color); break;
			case ROOK: GenPieceMoves(R_dirs, 1, 4, sq, pos, color); break;
			case QUEEN: GenPieceMoves(Q_dirs, 1, 8, sq, pos, color); break;
			case KING:
				GenPieceMoves(Q_dirs, 0, 8, sq, pos, color);
				if (!pos.IsCheck(color)) {
					if (pos.CanCastleQS(color))
						AddMove(sq, sq - 2);
					if (pos.CanCastleKS(color))
						AddMove(sq, sq + 2);
				}
				break;
			};
	}

	void ScoreMoves(Position& pos, const int color, int bestMove) {
		for (int i = 0; i < count; i++) {
			int dst = Dst(m_Moves[i]);
			int src = Src(m_Moves[i]);
			int piece = pos.board[src];
			int captured = pos.board[dst];
			int pc = piece & 0xf;
			m_Moves[i] += ((mm_pst[pc][board64[dst]] - mm_pst[pc][board64[src]]) << 17);
			//if (captured != EMPTY)m_Moves[i] += ((mm_value[TypeOf(captured)] - mm_value[TypeOf(piece)] / 10) << 17);
			if (captured != EMPTY)m_Moves[i] -= ((mm_value[TypeOf(piece)] / 10) << 17);
			if ((m_Moves[i] & 0xffff) == (bestMove & 0xffff))
				m_Moves[i] += (2048 << 17);
		}
	}

	int GetNextMove(int& nMove) {
		int Max = -1, Next = -1;
		for (int i = 0; i < count; i++)
			if (m_Moves[i] && Value(m_Moves[i]) > Max) {
				nMove = m_Moves[i];
				Next = i;
				Max = Value(nMove);
			}
		if (Next == -1) return 0;
		m_Moves[Next] = 0;
		return 1;
	}

};

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++)
		if (tt[n].hash)
			pm++;
	return pm;
}

static int CheckUp() {
	if (!(++info.nodes & 0xffff)) {
		if (info.timeLimit && (clock() - info.timeStart) > info.timeLimit)
			info.stop = true;
		if (info.nodesLimit && info.nodes > info.nodesLimit)
			info.stop = true;
	}
	return info.stop;
}

static bool IsRepetition(U64 hash) {
	for (int n = hash_count - 4; n >= 0; n -= 2)
		if (hash_history[n] == hash)
			return true;
	return false;
}

static string GetPv(Position& pos, int move) {
	Position npos = pos;
	string uci = " " + MoveToUci(move);
	npos.DoMove(move);
	if (npos.IsCheck(pos.color))
		return "";
	U64 hash = npos.GetHash();
	if (IsRepetition(hash))
		return uci;
	TTEntry entry = tt[hash % HASH_SIZE];
	if (!entry.move)
		return uci;
	string hashMove = MoveToUci(entry.move);
	Movelist moves{};
	moves.Generate(npos, 0);
	hash_history[hash_count++] = hash;
	for (int i = 0; i < moves.count; i++)
		if (MoveToUci(moves.m_Moves[i]) == hashMove)
			uci += GetPv(npos, entry.move);
	hash_count--;
	return uci;
}

static void PrintInfo(Position& board, int move, int depth, int score) {
	cout << "info depth " << depth << " score ";
	if (abs(score) < MATE - MAX_PLY)
		cout << "cp " << score;
	else
		cout << "mate " << (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1);
	cout << " time " << (clock() - info.timeStart) << " nodes " << info.nodes << " hashfull " << Permill() << " pv" << GetPv(board, move) << endl;
}

static void PrintBestMove(int move) {
	cout << "bestmove " << MoveToUci(move) << endl << flush;
}

static int SearchAlpha(Position& pos, int alpha, int beta, int depth, int ply, Stack* const stack, bool doNull = true) {
	int Color = pos.color, move;
	if (CheckUp())
		return 0;
	int static_eval = (pos.color == WHITE) ? pos.Evaluate() : -pos.Evaluate();
	if (ply >= MAX_PLY)
		return static_eval;
	bool in_check = pos.IsCheck(Color);
	if (in_check)
		depth = max(1, depth + 1);
	bool in_qsearch = depth <= 0;
	if (in_qsearch) {
		if (alpha < static_eval)
			alpha = static_eval;
		if (alpha >= beta)
			return beta;
	}
	else if (doNull && depth > 2 && !in_check
		//&& ((Color == WHITE && pos.WMat > 400) || (Color == BLACK && pos.BMat > 400))) {
		&& ((Color == WHITE && pos.phaseW > 1) || (Color == BLACK && pos.phaseB > 1))) {
		pos.color = Switch(pos.color);
		int score = -SearchAlpha(pos, -beta, -beta + 1, depth - 3, ply + 1, stack, false);
		pos.color = Switch(pos.color);
		if (score >= beta)
			return beta;
	}
	Movelist moves;
	moves.Generate(pos, in_qsearch);
	U64 hash = pos.GetHash();
	if (ply && !in_qsearch)
		if (pos.move50 >= 100 || IsRepetition(hash))
			return 0;
	TTEntry& tt_entry = tt[hash % HASH_SIZE];
	int tt_move = 0;
	if (tt_entry.hash == hash) {
		tt_move = tt_entry.move;
		if (ply > 0 && alpha == beta - 1 && tt_entry.depth >= depth) {
			if (tt_entry.flag == EXACT)
				return tt_entry.score;
			if (tt_entry.flag == LOWER && tt_entry.score <= alpha)
				return tt_entry.score;
			if (tt_entry.flag == UPPER && tt_entry.score >= beta)
				return tt_entry.score;
		}
	}
	else if (depth > 3)
		depth--;
	moves.ScoreMoves(pos, Color, tt_move);
	int best_move = tt_move;
	int best_score = -INF;
	U8 tt_flag = LOWER;
	hash_history[hash_count++] = hash;
	while (moves.GetNextMove(move)) {
		Position npos = pos;
		npos.DoMove(move);
		if (npos.IsCheck(Color)) continue;
		int score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1, stack);
		if (info.stop)
			break;
		if (best_score < score)
			best_score = score;
		if (alpha < score) {
			alpha = score;
			best_move = move;
			stack[ply].move = move;
			tt_flag = EXACT;
			if (!ply && info.post)
				PrintInfo(pos, move, depth, score);
			if (alpha >= beta) {
				tt_flag = UPPER;
				break;
			}
		}
	}
	hash_count--;
	if (info.stop)
		return 0;
	if (best_score == -INF)
		return in_qsearch ? alpha : in_check ? ply - MATE : 0;
	if (tt_entry.hash != hash || depth >= tt_entry.depth || tt_flag == EXACT) {
		tt_entry.hash = hash;
		tt_entry.move = !best_move ? tt_move : best_move;
		tt_entry.flag = tt_flag;
		tt_entry.score = best_score;
		tt_entry.depth = in_qsearch ? 0 : depth;
	}
	return alpha;
}

static void SearchIteratively(Position& pos) {
	memset(stack, 0, sizeof(stack));
	for (int depth = 1; depth <= info.depthLimit; depth++) {
		int score = SearchAlpha(pos, -MATE, MATE, depth, 0, stack);
		if (info.stop)
			break;
		if (info.timeLimit && ((clock() - info.timeStart) > (info.timeLimit / 2)))
			break;
		if (abs(score) >= (MATE - depth))
			break;
	}
	if (info.post)
		PrintBestMove(stack[0].move);
}

static void PrintBoard() {
	int r, f, sq;
	string uw = "ANBRQKXX";
	string ub = "anbrqkxx";
	string s = "   +---+---+---+---+---+---+---+---+";
	string t = "     A   B   C   D   E   F   G   H";
	cout << t << endl;
	for (r = 7; r >= 0; r--) {
		cout << s << endl;
		cout << " " << r + 1 << " |";
		for (f = 0; f <= 7; f++) {
			sq = Sq(f, 7 - r);
			int piece = pos.board[sq];
			if (!piece)
				cout << "   |";
			else if (piece & WHITE)
				cout << " " << uw[piece & 0x7] << " |";
			else if (piece & BLACK)
				cout << " " << ub[piece & 0x7] << " |";
		}
		cout << endl;
	}
	cout << s << endl;
	cout << t << endl;
	cout << "side : " << (pos.color == WHITE ? "white" : "black") << endl;
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

//displays a summary
static void PrintSummary(U64 time, U64 nodes) {
	U64 nps = (nodes * 1000) / max(time, 1ull);
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	U64 p = (int)pow(10, sn * 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

static void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

void ResetInfo() {
	info.stop = false;
	info.post = true;
	info.nodes = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.timeLimit = 0;
	info.timeStart = clock();
}

//start benchmark
static void UciBench(Position& pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	info.post = false;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		++info.depthLimit;
		SearchIteratively(pos);
		elapsed = clock() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

static void ParsePosition(string command) {
	string fen = START_FEN;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "position")
		return;
	ss >> token;
	if (token == "startpos")
		ss >> token;
	else if (token == "fen") {
		fen = "";
		while (ss >> token && token != "moves")
			fen += token + " ";
		fen.pop_back();
	}
	pos.SetFen(fen);
	hash_count = 0;
	while (ss >> token) {
		hash_history[hash_count++] = pos.GetHash();
		int move = UciToMove(token);
		pos.DoMove(move);
	}
}

static void ParseGo(string command) {
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "go")
		return;
	ResetInfo();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	char* argument = NULL;
	while (ss >> token) {
		if (token == "wtime")
			ss >> wtime;
		else if (token == "btime")
			ss >> btime;
		else if (token == "winc")
			ss >> winc;
		else if (token == "binc")
			ss >> binc;
		else if (token == "movestogo")
			ss >> movestogo;
		else if (token == "movetime")
			ss >> info.timeLimit;
		else if (token == "depth")
			ss >> info.depthLimit;
		else if (token == "nodes")
			ss >> info.nodesLimit;
	}
	int time = pos.color == WHITE ? wtime : btime;
	int inc = pos.color == WHITE ? winc : binc;
	if (time)
		info.timeLimit = min(time / movestogo + inc, time / 2);
	SearchIteratively(pos);
}

static void UciCommand(string command) {
	if (command.empty())
		return;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token == "uci")cout << "id name " << NAME << endl << "uciok" << endl;
	else if (token == "isready")cout << "readyok" << endl;
	else if (token == "ucinewgame")TTClear();
	else if (token == "print")PrintBoard();
	else if (token == "quit")exit(0);
	else if (token == "bench")UciBench(pos);
	else if (token == "position")ParsePosition(command);
	else if (token == "go")ParseGo(command);
}

static void UciLoop() {
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(line);
	}
}

static void InitHash() {
	mt19937_64 r;
	for (U64& k : keys)
		k = r();
}

int main() {
	cout << NAME << " " << VERSION << endl;
	InitEval();
	InitHash();
	pos.Init();
	pos.SetFen(START_FEN);
	UciLoop();
}