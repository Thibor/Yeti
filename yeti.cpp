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

const int HASH_SIZE = 1 << 21;
const int INVALID = 32, EMPTY = 0, WHITE = 8, BLACK = 16;
const int B_QS = 4, B_KS = 8, W_QS = 1, W_KS = 2;
const int N_dirs[8] = { -21, -19, -12, -8, 8, 12, 19, 21 };
const int Q_dirs[8] = { 1, -1, 9, -9, 10, -10, 11, -11 };
const int R_dirs[4] = { 1, -1,  -10, 10 };
const int B_dirs[4] = { 9, -9, -11, 11 };
const int P_dirs[8] = { -10, -20, -9, -11, 10, 20, 9, 11 };
int inline static SRC(int Move) { return (Move & 0x7f); }
int inline static DST(int Move) { return ((Move >> 7) & 0x7f); }
int inline static PROMO(int Move) { return ((Move >> 14) & 7); }
int inline static VALUE(int Move) { return ((Move >> 17) & 0x3fff); }
int inline static SWITCH(int Color) { return Color ^ (WHITE | BLACK); }
int inline static File(int Sq) { return (Sq - 20) % 10; }
int inline static Rank(int Sq) { return (Sq - 10) / 10; }
int inline static SQ(int file, int rank) { return 21 + file + rank * 10; }
int inline static RelativeRank(int Sq, int col) { return col == BLACK ? (Sq - 10) / 10 : 9 - (Sq - 10) / 10; }
int hash_count = 0;
U64 hash_history[2000]{};
U64 keys[128 * 16];
int EvalSq[26 * 128]{};
int SetCastle[120]{};
const int PieceValues[8] = { 100, 320, 330, 500, 900,0 };
const int KingEval[10] = { 0, 8, 12, 5, 0, 0, 5, 14, 9, 0 };
const int CentEval[10] = { 0,-6, -3, -1, 0, 0, -1, -3, -6, 0 };
const int Cent[10] = { 0, 1, 2, 2, 3, 3, 2, 1, 1, 0 };
Stack stack[MAX_PLY]{};
TTEntry tt[HASH_SIZE] {};

const string SQSTR[64] = {
	"a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1",
	"a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
	"a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
	"a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
	"a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
	"a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
	"a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
	"a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8"
};

static string SquareToStr(int sq) {
	int r = 8 - Rank(sq);
	int f = File(sq) - 1;
	sq = r * 8 + f;
	if (sq < 0 || sq>63)
		return "error";
	return SQSTR[sq];
}

static string MoveToUci(int move) {
	int src = SRC(move);
	int dst = DST(move);
	int promo = PROMO(move);
	string uci = SquareToStr(src) + SquareToStr(dst);
	if (promo < KING)
		uci += "pnbrqk"[promo];
	return uci;
}

static int UciToMove(string s) {
	int Src = SQ(s[0] - 'a', 7 - (s[1] - '1'));
	int Dst = SQ(s[2] - 'a', 7 - (s[3] - '1'));
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
	unsigned char board[120]{};

	int color = WHITE, Eval = 0, EPsq = 0, Castling = 0, WKsq = 95, BKsq = 25, WMat = 0, BMat = 0, nLastCapOrPawn = 0;

	void Clear() {
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
		for (pc = 0; pc < 8; pc++)
			for (sq = 0; sq < 120; sq++) {
				EvalSq[((pc | WHITE) << 7) + sq] = PieceValues[pc];
				EvalSq[((pc | BLACK) << 7) + sq] = -PieceValues[pc];
				if (pc == PAWN)
				{
					EvalSq[((pc | WHITE) << 7) + sq] += (9 - Rank(sq)) * Cent[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= Rank(sq) * Cent[File(sq)];
				}
				else if (pc == KING) {}
				else {
					if (pc != ROOK && Rank(sq) == 8) EvalSq[((pc | WHITE) << 7) + sq] -= 8;
					if (pc != ROOK && Rank(sq) == 1) EvalSq[((pc | BLACK) << 7) + sq] += 8;
					EvalSq[((pc | WHITE) << 7) + sq] += CentEval[File(sq)];
					EvalSq[((pc | BLACK) << 7) + sq] -= CentEval[File(sq)];
				}
				EvalSq[(0 << 7) + sq] = (Rank(sq) - 9) * 2 + KingEval[File(sq)];
				EvalSq[(1 << 7) + sq] = (Rank(sq)) * 2 - KingEval[File(sq)];
				EvalSq[(2 << 7) + sq] = 2 * CentEval[File(sq)];
				EvalSq[(3 << 7) + sq] = -2 * CentEval[File(sq)];
			}
	}

	void SetFen(string fen) {
		Eval = 0;
		WMat = BMat = 0;
		EPsq = 0;
		Castling = 0xf;
		Clear();
		int sq = 21;
		stringstream ss(fen);
		string token;
		ss >> token;
		for (char c : token)
			switch (c) {
			case 'p':Eval += EvalSq[((PAWN | BLACK) << 7) + sq]; board[sq] = PAWN | BLACK; Eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'n':Eval += EvalSq[((KNIGHT | BLACK) << 7) + sq]; BMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | BLACK; Eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'b':Eval += EvalSq[((BISHOP | BLACK) << 7) + sq]; BMat += PieceValues[BISHOP]; board[sq] = BISHOP | BLACK; Eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'r':Eval += EvalSq[((ROOK | BLACK) << 7) + sq]; BMat += PieceValues[ROOK]; board[sq] = ROOK | BLACK; Eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'q':Eval += EvalSq[((QUEEN | BLACK) << 7) + sq]; BMat += PieceValues[QUEEN]; board[sq] = QUEEN | BLACK; Eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'k':Eval += EvalSq[((KING | BLACK) << 7) + sq]; BKsq = sq;  board[sq] = KING | BLACK; sq++; Eval += EvalSq[(KING << 7) + sq]; break;
			case 'P':Eval += EvalSq[((PAWN | WHITE) << 7) + sq]; board[sq] = PAWN | WHITE; Eval += EvalSq[(PAWN << 7) + sq]; sq++; break;
			case 'N':Eval += EvalSq[((KNIGHT | WHITE) << 7) + sq]; WMat += PieceValues[KNIGHT]; board[sq] = KNIGHT | WHITE; Eval += EvalSq[(KNIGHT << 7) + sq]; sq++; break;
			case 'B':Eval += EvalSq[((BISHOP | WHITE) << 7) + sq]; WMat += PieceValues[BISHOP]; board[sq] = BISHOP | WHITE; Eval += EvalSq[(BISHOP << 7) + sq]; sq++; break;
			case 'R':Eval += EvalSq[((ROOK | WHITE) << 7) + sq]; WMat += PieceValues[ROOK]; board[sq] = ROOK | WHITE; Eval += EvalSq[(ROOK << 7) + sq]; sq++; break;
			case 'Q':Eval += EvalSq[((QUEEN | WHITE) << 7) + sq]; WMat += PieceValues[QUEEN]; board[sq] = QUEEN | WHITE; Eval += EvalSq[(QUEEN << 7) + sq]; sq++; break;
			case 'K':WKsq = sq; board[sq] = KING | WHITE; Eval += EvalSq[(KING << 7) + sq]; sq++; break;
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
			switch (c)
			{
			case 'K':
				Castling ^= W_KS;
				break;
			case 'Q':
				Castling ^= W_QS;
				break;
			case 'k':
				Castling ^= B_KS;
				break;
			case 'q':
				Castling ^= B_QS;
				break;
			}

		ss >> token;
		if (token != "-")
		{
			int file = token[0] - 'a';
			int rank = 7 - (token[1] - '1');
			EPsq = SQ(file, rank);
		}
	}

	int CanCastleKS(const int Color) const {
		if (Color == WHITE && !(Castling & W_KS) && board[WKsq + 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq + 1) && board[WKsq + 2] == EMPTY) return 1;
		if (Color == BLACK && !(Castling & B_KS) && board[BKsq + 1] == EMPTY && !ColorAttacksSq(WHITE, BKsq + 1) && board[BKsq + 2] == EMPTY) return 1;
		return 0;
	}

	int CanCastleQS(const int Color) const {
		if (Color == WHITE && !(Castling & W_QS) && board[WKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, WKsq - 1) && board[WKsq - 2] == EMPTY && board[WKsq - 3] == EMPTY) return 1;
		if (Color == BLACK && !(Castling & B_QS) && board[BKsq - 1] == EMPTY && !ColorAttacksSq(BLACK, BKsq - 1) && board[BKsq - 2] == EMPTY && board[BKsq - 3] == EMPTY) return 1;
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
		Eval += EvalSq[(piece << 7) + Dst] - EvalSq[(piece << 7) + Src];
		if (board[Dst] != EMPTY)
		{
			Eval -= EvalSq[(board[Dst] << 7) + Dst];
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
				Eval += EvalSq[(board[Dst] << 7) + Dst] - EvalSq[(piece << 7) + Dst];
			}
			if (Dst == EPsq) {
				EPsq = Src + File(Dst) - File(Src);
				Eval -= EvalSq[(board[EPsq] << 7) + EPsq];
				board[EPsq] = EMPTY;
			}
			if (abs(Src - Dst) == 20) EPsq = ((Src + Dst) >> 1); else EPsq = 0;
		}
		else EPsq = 0;
	}

	void DoMove(const int Move) {
		int Dst = DST(Move), Src = SRC(Move);
		Castling |= SetCastle[Src] | SetCastle[Dst];
		color = SWITCH(color);
		if ((board[Src] & 7) == KING) {
			if (Dst == Src - 2) { MovePiece(Src, Src - 2, 0); MovePiece(Src - 4, Src - 1, 0); return; }
			if (Dst == Src + 2) { MovePiece(Src, Src + 2, 0); MovePiece(Src + 3, Src + 1, 0); return; }
		}
		MovePiece(Src, Dst, PROMO(Move));
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
			return Eval + EvalSq[(2 << 7) + WKsq] + EvalSq[(3 << 7) + BKsq];
		return Eval + EvalSq[(0 << 7) + WKsq] + EvalSq[(1 << 7) + BKsq];
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
			if (Board.board[tempSq] & SWITCH(COLOR))
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
		if (Sq + P_dirs[n + 2] == Board.EPsq || (Board.board[Sq + P_dirs[n + 2]] & SWITCH(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 2], rank == 7);
		if (Sq + P_dirs[n + 3] == Board.EPsq || (Board.board[Sq + P_dirs[n + 3]] & SWITCH(COLOR))) AddAtkMove(Sq, Sq + P_dirs[n + 3], rank == 7);
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
			int Dst = DST(m_Moves[i]);
			int Src = SRC(m_Moves[i]);
			int Piece = Board.board[Src];
			if (Color == WHITE) m_Moves[i] += ((EvalSq[(Piece << 7) + Dst] - EvalSq[(Piece << 7) + Src]) << 17);
			if (Color == BLACK) m_Moves[i] -= ((EvalSq[(Piece << 7) + Dst] - EvalSq[(Piece << 7) + Src]) << 17);
			if ((m_Moves[i] & 65535) == (bestMove & 65535))
				m_Moves[i] += (2048 << 17);
		}
	}

	int GetNextMove(int& nMove) {
		int Max = -1, Next = -1;
		for (int i = 0; i < count; i++)
			if (m_Moves[i] && VALUE(m_Moves[i]) > Max) {
				nMove = m_Moves[i];
				Next = i;
				Max = VALUE(nMove);
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
	string uci =" " + MoveToUci(move);
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
		pos.color = SWITCH(pos.color);
		int score = -SearchAlpha(pos, -beta, -beta + 1, depth - 3, ply + 1, stack, false);
		pos.color = SWITCH(pos.color);
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
			sq = SQ(f, 7 - r);
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
	if (command.empty())
		return;
	if (command == "uci")
		cout << "id name " << NAME << endl << "uciok" << endl;
	else if (command == "isready")
		cout << "readyok" << endl;
	else if (command == "ucinewgame")
		TTClear();
	else if (command.substr(0, 8) == "position")
		ParsePosition(command);
	else if (command.substr(0, 2) == "go")
		ParseGo(command);
	else if (command == "print")
		PrintBoard();
	else if (command == "quit")
		exit(0);
}

static void UciLoop() {
	//UciCommand("position startpos moves e2e4 c7c5 g1f3 d7d6 d2d4 g8f6 d4c5 d8a5 c1d2 a5c5 b1c3 b8c6 f1d3 c8g4 e1g1 c6d4 d2e3 g4f3 g2f3 e7e5 c3b5 a7a6 b5d4 e5d4 e3d4 c5c6 f3f4 e8c8 e4e5 d6e5 f4e5 c8b8 c2c3 f6d7 d1e2 d7c5 d3c2 f8e7 a1d1 h8f8 c2h7 g7g6 d4c5 c6c5 d1d8 f8d8 b2b4 c5c3 e5e6 c3f6 f1e1 e7b4 e2e5 f6e5 e1e5 f7e6 h7g6 d8d2 a2a4 d2a2 g6e4 a2a4 e5e6 b4c5 g1g2 a4a2 e6f6 a2e2 e4d3 e2b2 g2f1 b2a2 f6f5 c5d4 f5f4 d4e5 f4f8 b8a7 h2h4 a2d2 d3e2 d2c2 e2d3 c2c1 f1e2 c1h1 f8f5 e5d4 d3e4 h1h4 e2d3 d4b6 f5f7 h4e4 d3e4 a6a5 e4d5 a7a6 f2f4 a5a4 f7e7 a4a3 f4f5 b6a5 e7e2 a5c3 f5f6 c3f6 e2e6 a6b5 e6f6 a3a2 f6f1 b5b4 d5e6 b4b3 f1e1 b3b2 e1e2 b2a3 e2e1 a3b2");
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(line);
	}
}

int main() {
	cout << NAME << " " << VERSION << endl;
	mt19937_64 r;
	for (U64& k : keys)
		k = r();
	pos.Init();
	pos.SetFen(START_FEN);
	UciLoop();
}