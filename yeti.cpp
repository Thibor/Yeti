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

enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { LOWER, UPPER, EXACT };

struct Stack {
	int move;
};

struct SearchInfo {
	int stop;
	int depthLimit;
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
const int N_dirs[8] = { -21, -19, -12, -8, 8, 12, 19, 21 };
const int Q_dirs[8] = { 1, -1, 9, -9, 10, -10, 11, -11 };
const int R_dirs[4] = { 1, -1,  -10, 10 };
const int B_dirs[4] = { 9, -9, -11, 11 };
const int P_dirs[8] = { -10, -20, -9, -11, 10, 20, 9, 11 };
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
U64 hash_history[2000]{};
U64 keys[128 * 16]{};
int EvalSq[26 * 128]{};
int SetCastle[120]{};
const int PieceValues[8] = { 100, 320, 330, 500, 900,0 };
const int KingEval[10] = { 0, 8, 12, 5, 0, 0, 5, 14, 9, 0 };
const int CentEval[10] = { 0,-6, -3, -1, 0, 0, -1, -3, -6, 0 };
const int Cent[10] = { 0, 1, 2, 2, 3, 3, 2, 1, 1, 0 };
Stack stack[MAX_PLY]{};
TTEntry tt[HASH_SIZE]{};

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
	int color, eval, EPsq, castling, WKsq, BKsq, WMat, BMat;

	void Clear() {
		color = eval = EPsq = WKsq = BKsq = WMat = BMat = 0;
		castling = 0xf;
		for (int x = 0; x < 10; x++)
			for (int y = 0; y < 12; y++)
				board[x + y * 10] = x > 0 && x < 9 && y>1 && y < 10 ? EMPTY : INVALID;
	}

	void Init() {
		int sq, pc;
		Clear();
		for (sq = 0; sq < 120; sq++)
			SetCastle[sq] = 0;
		SetCastle[21] = B_QS; SetCastle[28] = B_KS; SetCastle[25] = B_QS | B_KS;
		SetCastle[91] = W_QS; SetCastle[98] = W_KS; SetCastle[95] = W_QS | W_KS;
		for (sq = 0; sq < 120; sq++) {
			for (pc = 0; pc < PT_NB; pc++) {
				EvalSq[((pc | WHITE) << 7) + sq] = PieceValues[pc];
				EvalSq[((pc | BLACK) << 7) + sq] = -PieceValues[pc];
				if (pc == PAWN){
					EvalSq[((pc | WHITE) << 7) + sq] += (9 - Rank(sq)) * Cent[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= Rank(sq) * Cent[File(sq)];
				}else if (pc != KING) {
					if (pc != ROOK && Rank(sq) == 8)
						EvalSq[((pc | WHITE) << 7) + sq] -= 8;
					if (pc != ROOK && Rank(sq) == 1)
						EvalSq[((pc | BLACK) << 7) + sq] += 8;
					EvalSq[((pc | WHITE) << 7) + sq] += CentEval[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= CentEval[File(sq)];
				}
			}
			EvalSq[(0 << 7) + sq] = (Rank(sq) - 9) * 2 + KingEval[File(sq)];
			EvalSq[(1 << 7) + sq] = (Rank(sq)) * 2 - KingEval[File(sq)];
			EvalSq[(2 << 7) + sq] = 2 * CentEval[File(sq)];
			EvalSq[(3 << 7) + sq] = -2 * CentEval[File(sq)];
		}
	}

	void SetFen(string fen) {
		Clear();
		int sq = 21;
		stringstream ss(fen);
		string token;
		ss >> token;
		for (char c : token)
			switch (c) {
			case 'p':eval += EvalSq[((PAWN | BLACK) << 7) + sq]; board[sq] = PAWN | BLACK; eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'n':eval += EvalSq[((KNIGHT | BLACK) << 7) + sq]; BMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | BLACK; eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'b':eval += EvalSq[((BISHOP | BLACK) << 7) + sq]; BMat += PieceValues[BISHOP]; board[sq] = BISHOP | BLACK; eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'r':eval += EvalSq[((ROOK | BLACK) << 7) + sq]; BMat += PieceValues[ROOK]; board[sq] = ROOK | BLACK; eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'q':eval += EvalSq[((QUEEN | BLACK) << 7) + sq]; BMat += PieceValues[QUEEN]; board[sq] = QUEEN | BLACK; eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'k':eval += EvalSq[((KING | BLACK) << 7) + sq]; BKsq = sq;  board[sq] = KING | BLACK; sq++; eval += EvalSq[(KING << 7) + sq]; break;
			case 'P':eval += EvalSq[((PAWN | WHITE) << 7) + sq]; board[sq] = PAWN | WHITE; eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'N':eval += EvalSq[((KNIGHT | WHITE) << 7) + sq]; WMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | WHITE; eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'B':eval += EvalSq[((BISHOP | WHITE) << 7) + sq]; WMat += PieceValues[BISHOP]; board[sq] = BISHOP | WHITE; eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'R':eval += EvalSq[((ROOK | WHITE) << 7) + sq]; WMat += PieceValues[ROOK]; board[sq] = ROOK | WHITE; eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'Q':eval += EvalSq[((QUEEN | WHITE) << 7) + sq]; WMat += PieceValues[QUEEN]; board[sq] = QUEEN | WHITE; eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'K':WKsq = sq; board[sq] = KING | WHITE; eval += EvalSq[(KING << 7) + sq]; sq++; break;
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
		if (token != "-")
		{
			int file = token[0] - 'a';
			int rank = 7 - (token[1] - '1');
			EPsq = Sq(file, rank);
		}
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

	void AdjustMat(int Dst, const int Mul) {
		int pt = board[Dst] & 7;
		if (pt == PAWN) return;
		if (board[Dst] & WHITE)
			WMat += Mul * PieceValues[pt];
		else
			BMat += Mul * PieceValues[pt];
	}

	void MovePiece(const int Src, const int Dst, const int promo) {
		int piece = board[Src];
		eval += EvalSq[(piece << 7) + Dst] - EvalSq[(piece << 7) + Src];
		if (board[Dst] != EMPTY)
		{
			eval -= EvalSq[(board[Dst] << 7) + Dst];
			AdjustMat(Dst, -1);
		}
		board[Dst] = piece;
		board[Src] = EMPTY;
		if (piece == (KING | WHITE)) WKsq = Dst;
		if (piece == (KING | BLACK)) BKsq = Dst;
		if ((piece & 7) == PAWN) {
			if (Dst < 30 || Dst > 90) {
				board[Dst] += promo;
				AdjustMat(Dst, 1);
				eval += EvalSq[(board[Dst] << 7) + Dst] - EvalSq[(piece << 7) + Dst];
			}
			if (Dst == EPsq) {
				EPsq = Src + File(Dst) - File(Src);
				eval -= EvalSq[(board[EPsq] << 7) + EPsq];
				board[EPsq] = EMPTY;
			}
			if (abs(Src - Dst) == 20) EPsq = ((Src + Dst) >> 1); else EPsq = 0;
		}
		else EPsq = 0;
	}

	void DoMove(const int Move) {
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

	int Evaluate() const {
		if (WMat < 1400 && BMat < 1400)
			return eval + EvalSq[(2 << 7) + WKsq] + EvalSq[(3 << 7) + BKsq];
		return eval + EvalSq[(0 << 7) + WKsq] + EvalSq[(1 << 7) + BKsq];
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
	int count, m_nAttacks, m_onlyCapture;
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
			m_Moves[count++] = Src + (Dst << 7) + (PT_NB << 14) + ((200 + PieceValues[(m_board[Dst] & 7)]) << 17);
	}

	void inline AddPromoMove(int Src, int Dst) {
		m_Moves[count++] = Src + (Dst << 7) + (KNIGHT << 14) + ((200 + PieceValues[KNIGHT]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (BISHOP << 14) + ((200 + PieceValues[BISHOP]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (ROOK << 14) + ((200 + PieceValues[ROOK]) << 17);
		m_Moves[count++] = Src + (Dst << 7) + (QUEEN << 14) + ((200 + PieceValues[QUEEN]) << 17);
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

	void ScoreMoves(Position& Board, const int Color, int bestMove) {
		for (int i = 0; i < count; i++) {
			int dst = Dst(m_Moves[i]);
			int src = Src(m_Moves[i]);
			int Piece = Board.board[src];
			if (Color == WHITE) m_Moves[i] += ((EvalSq[(Piece << 7) + dst] - EvalSq[(Piece << 7) + src]) << 17);
			if (Color == BLACK) m_Moves[i] -= ((EvalSq[(Piece << 7) + dst] - EvalSq[(Piece << 7) + src]) << 17);
			if ((m_Moves[i] & 65535) == (bestMove & 65535))
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
	int Color = pos.color, NextBest = 0, move;
	if (CheckUp())
		return 0;
	int static_eval = (pos.color == WHITE) ? pos.Evaluate() : -pos.Evaluate();
	if (ply >= MAX_PLY)
		return static_eval;
	bool in_check = pos.IsCheck(Color);
	depth += in_check;
	bool in_qsearch = depth <= 0;
	if (in_qsearch) {
		if (alpha < static_eval)
			alpha = static_eval;
		if (alpha >= beta)
			return beta;
	}
	else if (doNull && depth > 2 && !in_check
		&& ((Color == WHITE && pos.WMat > 400) || (Color == BLACK && pos.BMat > 400))) {
		pos.color = Switch(pos.color);
		int score = -SearchAlpha(pos, -beta, -beta + 1, depth - 3, ply + 1, stack, false);
		pos.color = Switch(pos.color);
		if (score >= beta)
			return beta;
	}
	Movelist moves;
	moves.Generate(pos, in_qsearch);
	U64 hash = pos.GetHash();
	if (ply > 0 && !in_qsearch)
		if (IsRepetition(hash))
			return 0;
	TTEntry& tt_entry = tt[hash % HASH_SIZE];
	int tt_move = 0;
	if (tt_entry.hash == hash) {
		tt_move = tt_entry.move;
		if (ply > 0 && tt_entry.depth >= depth) {
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
	int best_move = 0;
	int best_score = -INF;
	U8 tt_flag = LOWER;
	hash_history[hash_count++] = hash;
	while (moves.GetNextMove(move)) {
		Position npos = pos;
		npos.DoMove(move);
		if (npos.IsCheck(Color)) continue;
		NextBest = 0;
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
			if (!ply)
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
	info.stop = false;
	info.nodes = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.timeLimit = 0;
	info.timeStart = clock();
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
	if (command == "uci")cout << "id name " << NAME << endl << "uciok" << endl;
	else if (command == "isready")cout << "readyok" << endl;
	else if (command == "ucinewgame")TTClear();
	else if (command == "print")PrintBoard();
	else if (command == "quit")exit(0);
	else if (command.substr(0, 8) == "position")ParsePosition(command);
	else if (command.substr(0, 2) == "go")ParseGo(command);
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
	InitHash();
	pos.Init();
	pos.SetFen(START_FEN);
	UciLoop();
}