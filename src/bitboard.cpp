/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2015 Marco Costalba, Joona Kiiski, Tord Romstad
  Copyright (C) 2015-2020 Marco Costalba, Joona Kiiski, Gary Linscott, Tord Romstad

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <bitset>

#include "bitboard.h"
#include "magic.h"
#include "misc.h"
#include "piece.h"

uint8_t PopCnt16[1 << 16];
uint8_t SquareDistance[SQUARE_NB][SQUARE_NB];

// added from Musketeer-Stockfish
Bitboard FileBB[FILE_NB];
Bitboard RankBB[RANK_NB];
//
  
Bitboard SquareBB[SQUARE_NB];
Bitboard LineBB[SQUARE_NB][SQUARE_NB];
Bitboard PseudoAttacks[COLOR_NB][PIECE_TYPE_NB][SQUARE_NB];
Bitboard PseudoMoves[COLOR_NB][PIECE_TYPE_NB][SQUARE_NB];
Bitboard LeaperAttacks[COLOR_NB][PIECE_TYPE_NB][SQUARE_NB];
Bitboard LeaperMoves[COLOR_NB][PIECE_TYPE_NB][SQUARE_NB];

Bitboard BoardSizeBB[FILE_NB][RANK_NB];
RiderType AttackRiderTypes[PIECE_TYPE_NB];
RiderType MoveRiderTypes[PIECE_TYPE_NB];


Magic RookMagicsH[SQUARE_NB];
Magic RookMagicsV[SQUARE_NB];

// in Musketeer-Stockfish RookMagics[SQUARE_NB]

Magic BishopMagics[SQUARE_NB];
Magic CannonMagicsH[SQUARE_NB];
Magic CannonMagicsV[SQUARE_NB];
Magic HorseMagics[SQUARE_NB];
Magic ElephantMagics[SQUARE_NB];

namespace {

#ifdef LARGEBOARDS
  Bitboard RookTableH[0x11800];  // To store horizontalrook attacks
  Bitboard RookTableV[0x4800];  // To store vertical rook attacks
  Bitboard BishopTable[0x33C00]; // To store bishop attacks
  Bitboard CannonTableH[0x11800];  // To store horizontal cannon attacks
  Bitboard CannonTableV[0x4800];  // To store vertical cannon attacks
  Bitboard HorseTable[0x500];  // To store horse attacks
  Bitboard ElephantTable[0x400];  // To store elephant attacks
#else
  Bitboard RookTableH[0xA00];  // To store horizontal rook attacks
  Bitboard RookTableV[0xA00];  // To store vertical rook attacks
  Bitboard BishopTable[0x1480]; // To store bishop attacks
  Bitboard CannonTableH[0xA00];  // To store horizontal cannon attacks
  Bitboard CannonTableV[0xA00];  // To store vertical cannon attacks
  Bitboard HorseTable[0x240];  // To store horse attacks
  Bitboard ElephantTable[0x1A0];  // To store elephant attacks
#endif

  enum MovementType { RIDER, HOPPER, LAME_LEAPER };

  template <MovementType MT>
#ifdef PRECOMPUTED_MAGICS
  void init_magics(Bitboard table[], Magic magics[], std::vector<Direction> directions, Bitboard magicsInit[]);
#else
  void init_magics(Bitboard table[], Magic magics[], std::vector<Direction> directions);
#endif
  
  // Added from Musketeer-Stockfish
  // popcount16() counts the non-zero bits using SWAR-Popcount algorithm



  unsigned popcount16(unsigned u) {

    u -= (u >> 1) & 0x5555U;

    u = ((u >> 2) & 0x3333U) + (u & 0x3333U);

    u = ((u >> 4) + u) & 0x0F0FU;

    return (u * 0x0101U) >> 8;

  }
  // End added code from Musketeer-Stockfish

    
  template <MovementType MT>
  Bitboard sliding_attack(std::vector<Direction> directions, Square sq, Bitboard occupied, Color c = WHITE) {
    assert(MT != LAME_LEAPER);

    Bitboard attack = 0;

    for (Direction d : directions)
    {
        bool hurdle = false;
        for (Square s = sq + (c == WHITE ? d : -d);
             is_ok(s) && distance(s, s - (c == WHITE ? d : -d)) == 1;
             s += (c == WHITE ? d : -d))
        {
            if (MT != HOPPER || hurdle)
                attack |= s;

            if (occupied & s)
            {
                if (MT == HOPPER && !hurdle)
                    hurdle = true;
                else
                    break;
            }
        }
    }

    return attack;
  }


  Bitboard lame_leaper_path(Direction d, Square s) {
    Direction dr = d > 0 ? NORTH : SOUTH;
    Direction df = (std::abs(d % NORTH) < NORTH / 2 ? d % NORTH : -(d % NORTH)) < 0 ? WEST : EAST;
    Square to = s + d;
    Bitboard b = 0;
    if (!is_ok(to) || distance(s, to) >= 4)
        return b;
    while (s != to)
    {
        int diff = std::abs(file_of(to) - file_of(s)) - std::abs(rank_of(to) - rank_of(s));
        if (diff > 0)
            s += df;
        else if (diff < 0)
            s += dr;
        else
            s += df + dr;

        if (s != to)
            b |= s;
    }
    return b;
  }
  
  

  Bitboard lame_leaper_path(std::vector<Direction> directions, Square s) {
    Bitboard b = 0;
    for (Direction d : directions)
        b |= lame_leaper_path(d, s);
    return b;
  }
  
  

  Bitboard lame_leaper_attack(std::vector<Direction> directions, Square s, Bitboard occupied) {
    Bitboard b = 0;
    for (Direction d : directions)
    {
        Square to = s + d;
        if (is_ok(to) && distance(s, to) < 4 && !(lame_leaper_path(d, s) & occupied))
            b |= to;
    }
    return b;
  }
}


// Code from Fairy

  Bitboard sliding_attack(Direction directions[], Square sq, Bitboard occupied, int max_dist = 7) {



    Bitboard attack = 0;



    for (int i = 0; directions[i]; ++i)

        for (Square s = sq + directions[i];

             is_ok(s) && distance(s, s - directions[i]) == 1 && distance(s, sq) <= max_dist;

             s += directions[i])

        {

            attack |= s;



            if (occupied & s)

                break;

        }



    return attack;

  }

}

// End code from fairy
  
  

/// Bitboards::pretty() returns an ASCII representation of a bitboard suitable
/// to be printed to standard output. Useful for debugging.

const std::string Bitboards::pretty(Bitboard b) {

  std::string s = "+---+---+---+---+---+---+---+---+---+---+---+---+\n";

  for (Rank r = RANK_MAX; r >= RANK_1; --r)
    
    // Rank r = RANK_8 'for Musketeer Chess'
    
  {
      for (File f = FILE_A; f <= FILE_MAX; ++f)
        
    //       for (File f = FILE_A; f <= FILE_H; ++f) 'for Musketeer Chess'
     
          s += b & make_square(f, r) ? "| X " : "|   ";

      s += "|\n+---+---+---+---+---+---+---+---+---+---+---+---+\n";
  }

  return s;
}


/// Bitboards::init() initializes various bitboard tables. It is called at
/// startup and relies on global objects to be already zero-initialized.

void Bitboards::init() {
  // Beginning of code added in Fairy-Stockfish

  // Initialize rider types
  for (PieceType pt = PAWN; pt <= KING; ++pt)
  {
      const PieceInfo* pi = pieceMap.find(pt)->second;

      if (pi->lameLeaper)
      {
          for (Direction d : pi->stepsCapture)
          {
              if (   d == 2 * SOUTH + WEST || d == 2 * SOUTH + EAST || d == SOUTH + 2 * WEST || d == SOUTH + 2 * EAST
                  || d == NORTH + 2 * WEST || d == NORTH + 2 * EAST || d == 2 * NORTH + WEST || d == 2 * NORTH + EAST)
                  AttackRiderTypes[pt] |= RIDER_HORSE;
              if (d == 2 * NORTH_EAST || d == 2 * SOUTH_EAST || d == 2 * SOUTH_WEST || d == 2 * NORTH_WEST)
                  AttackRiderTypes[pt] |= RIDER_ELEPHANT;
          }
          for (Direction d : pi->stepsQuiet)
          {
              if (   d == 2 * SOUTH + WEST || d == 2 * SOUTH + EAST || d == SOUTH + 2 * WEST || d == SOUTH + 2 * EAST
                  || d == NORTH + 2 * WEST || d == NORTH + 2 * EAST || d == 2 * NORTH + WEST || d == 2 * NORTH + EAST)
                  MoveRiderTypes[pt] |= RIDER_HORSE;
              if (d == 2 * NORTH_EAST || d == 2 * SOUTH_EAST || d == 2 * SOUTH_WEST || d == 2 * NORTH_WEST)
                  MoveRiderTypes[pt] |= RIDER_ELEPHANT;
          }
      }
      for (Direction d : pi->sliderCapture)
      {
          if (d == NORTH_EAST || d == SOUTH_WEST || d == NORTH_WEST || d == SOUTH_EAST)
              AttackRiderTypes[pt] |= RIDER_BISHOP;
          if (d == EAST || d == WEST)
              AttackRiderTypes[pt] |= RIDER_ROOK_H;
          if (d == NORTH || d == SOUTH)
              AttackRiderTypes[pt] |= RIDER_ROOK_V;
      }
      for (Direction d : pi->sliderQuiet)
      {
          if (d == NORTH_EAST || d == SOUTH_WEST || d == NORTH_WEST || d == SOUTH_EAST)
              MoveRiderTypes[pt] |= RIDER_BISHOP;
          if (d == EAST || d == WEST)
              MoveRiderTypes[pt] |= RIDER_ROOK_H;
          if (d == NORTH || d == SOUTH)
              MoveRiderTypes[pt] |= RIDER_ROOK_V;
      }
      for (Direction d : pi->hopperCapture)
      {
          if (d == EAST || d == WEST)
              AttackRiderTypes[pt] |= RIDER_CANNON_H;
          if (d == NORTH || d == SOUTH)
              AttackRiderTypes[pt] |= RIDER_CANNON_V;
      }
      for (Direction d : pi->hopperQuiet)
      {
          if (d == EAST || d == WEST)
              MoveRiderTypes[pt] |= RIDER_CANNON_H;
          if (d == NORTH || d == SOUTH)
              MoveRiderTypes[pt] |= RIDER_CANNON_V;
      }
  }
  
  // End Code Added in Fairy-Stockfish
  
  // Musketeer
  for (unsigned i = 0; i < (1 << 16); ++i)
      PopCnt16[i] = (uint8_t) popcount16(i);

  for (Square s = SQ_A1; s <= SQ_MAX; ++s)   // s <= SQ_H8 in Musketeer
      SquareBB[s] = make_bitboard(s);

  for (File f = FILE_A; f <= FILE_MAX; ++f)  // f <= FILE_H8 in Musketeer
  // Musketeer       FileBB[f] = f > FILE_A ? FileBB[f - 1] << 1 : FileABB;
  // Fairy Code, remember that Fairy wasn't programmed for Musketeer but for Drop pieces like in Seirawan. 
  //Size of the Board is also different, as Fairy supports bigger boards than 8x8
    
    for (Rank r = RANK_1; r <= RANK_MAX; ++r)
          BoardSizeBB[f][r] = forward_file_bb(BLACK, make_square(f, r)) | SquareBB[make_square(f, r)] | (f > FILE_A ? BoardSizeBB[f - 1][r] : Bitboard(0));

  // Musketeer for (Rank r = RANK_1; r <= RANK_8; ++r)
  // Musketeer    RankBB[r] = r > RANK_1 ? RankBB[r - 1] << 8 : Rank1BB;

  for (Square s1 = SQ_A1; s1 <= SQ_MAX; ++s1)  // Musketeer s1 <= SQ_H8
      for (Square s2 = SQ_A1; s2 <= SQ_MAX; ++s2)  // Musketeer s2 <= SQ_H8
  // Fairy in Musketeer it's 3 code lines beginning if (s1 = !s2)            SquareDistance[s1][s2] = std::max(distance<File>(s1, s2), distance<Rank>(s1, s2));
          if (s1 != s2)  // Musketeer
          {              // Musketeer
              SquareDistance[s1][s2] = std::max(distance<File>(s1, s2), distance<Rank>(s1, s2));  // Musketeer
              DistanceRingBB[s1][SquareDistance[s1][s2] - 1] |= s2;                               // Musketeer
          }                                                                                       // Musketeer
  
  for (Color c = WHITE; c <= BLACK; ++c)     // Musketeer
      for (Square s = SQ_A1; s <= SQ_MAX; ++s) // Musketeer Code normally s <= SQ_H8
          {
          ForwardFileBB [c][s] = ForwardRanksBB[c][rank_of(s)] & FileBB[file_of(s)];
          PawnAttackSpan[c][s] = ForwardRanksBB[c][rank_of(s)] & AdjacentFilesBB[file_of(s)];
          PassedPawnMask[c][s] = ForwardFileBB [c][s] | PawnAttackSpan[c][s];
          }                                  // End Added Musketeer Code

  
  
  
  
  
  
  
 
  // Piece moves
  std::vector<Direction> RookDirectionsV = { NORTH, SOUTH};
  std::vector<Direction> RookDirectionsH = { EAST, WEST };
  std::vector<Direction> BishopDirections = { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST };
  std::vector<Direction> HorseDirections = {2 * SOUTH + WEST, 2 * SOUTH + EAST, SOUTH + 2 * WEST, SOUTH + 2 * EAST,
                                            NORTH + 2 * WEST, NORTH + 2 * EAST, 2 * NORTH + WEST, 2 * NORTH + EAST };
  std::vector<Direction> ElephantDirections = { 2 * NORTH_EAST, 2 * SOUTH_EAST, 2 * SOUTH_WEST, 2 * NORTH_WEST };

#ifdef PRECOMPUTED_MAGICS
  init_magics<RIDER>(RookTableH, RookMagicsH, RookDirectionsH, RookMagicHInit);
  init_magics<RIDER>(RookTableV, RookMagicsV, RookDirectionsV, RookMagicVInit);
  init_magics<RIDER>(BishopTable, BishopMagics, BishopDirections, BishopMagicInit);
  init_magics<HOPPER>(CannonTableH, CannonMagicsH, RookDirectionsH, CannonMagicHInit);
  init_magics<HOPPER>(CannonTableV, CannonMagicsV, RookDirectionsV, CannonMagicVInit);
  init_magics<LAME_LEAPER>(HorseTable, HorseMagics, HorseDirections, HorseMagicInit);
  init_magics<LAME_LEAPER>(ElephantTable, ElephantMagics, ElephantDirections, ElephantMagicInit);
#else
  init_magics<RIDER>(RookTableH, RookMagicsH, RookDirectionsH);
  init_magics<RIDER>(RookTableV, RookMagicsV, RookDirectionsV);
  init_magics<RIDER>(BishopTable, BishopMagics, BishopDirections);
  init_magics<HOPPER>(CannonTableH, CannonMagicsH, RookDirectionsH);
  init_magics<HOPPER>(CannonTableV, CannonMagicsV, RookDirectionsV);
  init_magics<LAME_LEAPER>(HorseTable, HorseMagics, HorseDirections);
  init_magics<LAME_LEAPER>(ElephantTable, ElephantMagics, ElephantDirections);
#endif

  for (Color c : { WHITE, BLACK })
      for (PieceType pt = PAWN; pt <= KING; ++pt)
      {
          const PieceInfo* pi = pieceMap.find(pt)->second;

          for (Square s = SQ_A1; s <= SQ_MAX; ++s)
          {
              for (Direction d : pi->stepsCapture)
              {
                  Square to = s + Direction(c == WHITE ? d : -d);

                  if (is_ok(to) && distance(s, to) < 4)
                  {
                      PseudoAttacks[c][pt][s] |= to;
                      if (!pi->lameLeaper)
                          LeaperAttacks[c][pt][s] |= to;
                  }
              }
              for (Direction d : pi->stepsQuiet)
              {
                  Square to = s + Direction(c == WHITE ? d : -d);

                  if (is_ok(to) && distance(s, to) < 4)
                  {
                      PseudoMoves[c][pt][s] |= to;
                      if (!pi->lameLeaper)
                          LeaperMoves[c][pt][s] |= to;
                  }
              }
              PseudoAttacks[c][pt][s] |= sliding_attack<RIDER>(pi->sliderCapture, s, 0, c);
              PseudoAttacks[c][pt][s] |= sliding_attack<RIDER>(pi->hopperCapture, s, 0, c);
              PseudoMoves[c][pt][s] |= sliding_attack<RIDER>(pi->sliderQuiet, s, 0, c);
              PseudoMoves[c][pt][s] |= sliding_attack<RIDER>(pi->hopperQuiet, s, 0, c);
          }
      }

  for (Square s1 = SQ_A1; s1 <= SQ_MAX; ++s1)
  {
      for (PieceType pt : { BISHOP, ROOK })
          for (Square s2 = SQ_A1; s2 <= SQ_MAX; ++s2)
              if (PseudoAttacks[WHITE][pt][s1] & s2)
                  LineBB[s1][s2] = (attacks_bb(WHITE, pt, s1, 0) & attacks_bb(WHITE, pt, s2, 0)) | s1 | s2;
  }
}




// Musketeer Piece Moves
 Direction RookDirections[5] = { NORTH,  EAST,  SOUTH,  WEST };

 Direction BishopDirections[5] = { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST };

 init_magics(RookTable, RookMagics, RookDirections);

 init_magics(BishopTable, BishopMagics, BishopDirections);



  int steps[][17] = {

    {}, // NO_PIECE_TYPE

    { 7, 9 }, // Pawn

    { -17, -15, -10, -6, 6, 10, 15, 17 }, // Knight

    {}, // Bishop

    {}, // Rook

    {}, // Queen

    { -16, -10, -9, -8, -7, -6, -2, -1,

       16,  10,  9,  8,  7,  6,  2,  1 }, // Cannon

    { -17, -15, -10, -6, 6, 10, 15, 17 }, // Leopard

    { -17, -15, -10, -6, 6, 10, 15, 17 }, // Archbishop

    { -17, -15, -10, -6, 6, 10, 15, 17 }, // Chancellor

    { -17, -16, -15, -10, -6, -2,

       17,  16,  15,  10,  6,  2 }, // Spider

    { -17, -15, -10, -6, 6, 10, 15, 17 }, // Dragon

    { -25, -23, -17, -15, -11, -10, -6, -5,

       25,  23,  17,  15,  11,  10,  6,  5}, // Unicorn

    { -27, -24, -21, -18, -16, -14, -3, -2,

       27,  24,  21,  18,  16,  14,  3,  2 }, // Hawk

    { -18, -16, -14, -9, -8, -7, -2, -1,

       18,  16,  14,  9,  8,  7,  2,  1 }, // Elephant

    { -17, -16, -15, -2,

       17,  16,  15,  2 }, // Fortress

    { -9, -8, -7, -1, 1, 7, 8, 9 } // King

  };

  Direction slider[][9] = {

    {}, // NO_PIECE_TYPE

    {}, // Pawn

    {}, // Knight

    { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Bishop

    { NORTH,  EAST,  SOUTH,  WEST }, // Rook

    { NORTH,  EAST,  SOUTH,  WEST, NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Queen

    {}, // Cannon

    { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Leopard

    { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Archbishop

    { NORTH,  EAST,  SOUTH,  WEST }, // Chancellor

    { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Spider

    { NORTH,  EAST,  SOUTH,  WEST, NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Dragon

    {}, // Unicorn

    {}, // Hawk

    {}, // Elephant

    { NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST }, // Fortress

    {} // King

  };

  int slider_dist[] = {

    0, // NO_PIECE_TYPE

    0, // Pawn

    0, // Knight

    7, // Bishop

    7, // Rook

    7, // Queen

    0, // Cannon

    2, // Leopard

    7, // Archbishop

    7, // Chancellor

    2, // Spider

    7, // Dragon

    0, // Unicorn

    0, // Hawk

    0, // Elephant

    3, // Fortress

    0  // King

  };



  for (Color c = WHITE; c <= BLACK; ++c)

      for (PieceType pt = PAWN; pt <= KING; ++pt)

          for (Square s = SQ_A1; s <= SQ_H8; ++s)

          {

              for (int i = 0; steps[pt][i]; ++i)

              {

                  Square to = s + Direction(c == WHITE ? steps[pt][i] : -steps[pt][i]);



                  if (is_ok(to) && distance(s, to) < 4)

                  {

                      PseudoAttacks[c][pt][s] |= to;

                      LeaperAttacks[c][pt][s] |= to;

                  }

              }

              PseudoAttacks[c][pt][s] |= sliding_attack(slider[pt], s, 0, slider_dist[pt]);

          }



  for (Square s1 = SQ_A1; s1 <= SQ_H8; ++s1)

  {

      for (PieceType pt : { BISHOP, ROOK })

          for (Square s2 = SQ_A1; s2 <= SQ_H8; ++s2)

          {

              if (!(PseudoAttacks[WHITE][pt][s1] & s2))

                  continue;



              LineBB[s1][s2] = (attacks_bb(WHITE, pt, s1, 0) & attacks_bb(WHITE, pt, s2, 0)) | s1 | s2;

              BetweenBB[s1][s2] = attacks_bb(WHITE, pt, s1, SquareBB[s2]) & attacks_bb(WHITE, pt, s2, SquareBB[s1]);

          }

  }

}

// End Musketeer Piece Moves




namespace {

  // init_magics() computes all rook and bishop attacks at startup. Magic
  // bitboards are used to look up attacks of sliding pieces. As a reference see
  // www.chessprogramming.org/Magic_Bitboards. In particular, here we use the so
  // called "fancy" approach.

  template <MovementType MT>
#ifdef PRECOMPUTED_MAGICS
  void init_magics(Bitboard table[], Magic magics[], std::vector<Direction> directions, Bitboard magicsInit[]) {
#else
  void init_magics(Bitboard table[], Magic magics[], std::vector<Direction> directions) {
#endif

    // Optimal PRNG seeds to pick the correct magics in the shortest time
#ifndef PRECOMPUTED_MAGICS
#ifdef LARGEBOARDS
    int seeds[][RANK_NB] = { { 734, 10316, 55013, 32803, 12281, 15100,  16645, 255, 346, 89123 },
                             { 734, 10316, 55013, 32803, 12281, 15100,  16645, 255, 346, 89123 } };
#else
    int seeds[][RANK_NB] = { { 8977, 44560, 54343, 38998,  5731, 95205, 104912, 17020 },
                             {  728, 10316, 55013, 32803, 12281, 15100,  16645,   255 } };
#endif
#endif

    Bitboard* occupancy = new Bitboard[1 << (FILE_NB + RANK_NB - 4)];
    Bitboard* reference = new Bitboard[1 << (FILE_NB + RANK_NB - 4)];
    Bitboard edges, b;
    int* epoch = new int[1 << (FILE_NB + RANK_NB - 4)]();
    int cnt = 0, size = 0;


    for (Square s = SQ_A1; s <= SQ_MAX; ++s)
    {
        // Board edges are not considered in the relevant occupancies
        edges = ((Rank1BB | rank_bb(RANK_MAX)) & ~rank_bb(s)) | ((FileABB | file_bb(FILE_MAX)) & ~file_bb(s));

        // Given a square 's', the mask is the bitboard of sliding attacks from
        // 's' computed on an empty board. The index must be big enough to contain
        // all the attacks for each possible subset of the mask and so is 2 power
        // the number of 1s of the mask. Hence we deduce the size of the shift to
        // apply to the 64 or 32 bits word to get the index.
        Magic& m = magics[s];
        m.mask  = (MT == LAME_LEAPER ? lame_leaper_path(directions, s) : sliding_attack<MT == HOPPER ? RIDER : MT>(directions, s, 0)) & ~edges;
#ifdef LARGEBOARDS
        m.shift = 128 - popcount(m.mask);
#else
        m.shift = (Is64Bit ? 64 : 32) - popcount(m.mask);
#endif

        // Set the offset for the attacks table of the square. We have individual
        // table sizes for each square with "Fancy Magic Bitboards".
        m.attacks = s == SQ_A1 ? table : magics[s - 1].attacks + size;

        // Use Carry-Rippler trick to enumerate all subsets of masks[s] and
        // store the corresponding sliding attack bitboard in reference[].
        b = size = 0;
        do {
            occupancy[size] = b;
            reference[size] = MT == LAME_LEAPER ? lame_leaper_attack(directions, s, b) : sliding_attack<MT>(directions, s, b);

            if (HasPext)
                m.attacks[pext(b, m.mask)] = reference[size];

            size++;
            b = (b - m.mask) & m.mask;
        } while (b);

        if (HasPext)
            continue;

#ifndef PRECOMPUTED_MAGICS
        PRNG rng(seeds[Is64Bit][rank_of(s)]);
#endif

        // Find a magic for square 's' picking up an (almost) random number
        // until we find the one that passes the verification test.
        for (int i = 0; i < size; )
        {
            for (m.magic = 0; popcount((m.magic * m.mask) >> (SQUARE_NB - FILE_NB)) < FILE_NB - 2; )
            {
#ifdef LARGEBOARDS
#ifdef PRECOMPUTED_MAGICS
                m.magic = magicsInit[s];
#else
                m.magic = (rng.sparse_rand<Bitboard>() << 64) ^ rng.sparse_rand<Bitboard>();
#endif
#else
                m.magic = rng.sparse_rand<Bitboard>();
#endif
            }

            // A good magic must map every possible occupancy to an index that
            // looks up the correct sliding attack in the attacks[s] database.
            // Note that we build up the database for square 's' as a side
            // effect of verifying the magic. Keep track of the attempt count
            // and save it in epoch[], little speed-up trick to avoid resetting
            // m.attacks[] after every failed attempt.
            for (++cnt, i = 0; i < size; ++i)
            {
                unsigned idx = m.index(occupancy[i]);

                if (epoch[idx] < cnt)
                {
                    epoch[idx] = cnt;
                    m.attacks[idx] = reference[i];
                }
                else if (m.attacks[idx] != reference[i])
                    break;
            }
        }
    }

    delete[] occupancy;
    delete[] reference;
    delete[] epoch;
  }
}
