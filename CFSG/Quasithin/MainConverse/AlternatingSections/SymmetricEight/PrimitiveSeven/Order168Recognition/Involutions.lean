module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition.Generators
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

/-!
# Recognition from a seven-cycle and an even involution

An even involution on seven letters is a double transposition. For each
choice of its four distinct letters, the finite table records either a
conjugate, by a power of the seven-cycle, of one of six representatives,
or a word of order five. Every recorded identity is checked by the kernel.
Short words in the six surviving representatives give one of the two seed
involutions. Lagrange's theorem excludes the order-five outcome in a group
of order 168.

The table stores `6*k + r` for the conjugacy outcome (values below 42),
and `42 + 7*i + j` for the word c^i*t*c^j*t of order five. Repeated-letter
entries are unused. Thus the table supplies witnesses, not group axioms
or an assumed list of primitive subgroups.

This is the finite permutation step in the alternating examples' condition
(K) calculation, Aschbacher–Smith, printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse.Order168Recognition

open Equiv
private abbrev P := Equiv.Perm (Fin 7)
private abbrev c := cycle
private def reps : Fin 6 → P := ![
  swap 2 3 * swap 4 6,
  swap 2 4 * swap 5 6,
  swap 2 4 * swap 3 6,
  swap 2 5 * swap 4 6,
  swap 2 6 * swap 4 5,
  swap 2 6 * swap 3 4]
private def certificate (a b d e : Fin 7) : Fin 91 :=
  ![![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 50, 30, 22, 52],
    ![0, 0, 50, 0, 50, 53, 29],
    ![0, 0, 30, 50, 0, 50, 13],
    ![0, 0, 22, 53, 50, 0, 50],
    ![0, 0, 52, 29, 13, 50, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 53, 32, 21, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 53, 0, 0, 31, 53, 51],
    ![0, 32, 0, 31, 0, 53, 53],
    ![0, 21, 0, 53, 53, 0, 18],
    ![0, 53, 0, 51, 53, 18, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 52, 0, 51, 51, 26],
    ![0, 52, 0, 0, 33, 51, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 51, 33, 0, 0, 11, 51],
    ![0, 51, 51, 0, 11, 0, 10],
    ![0, 26, 51, 0, 51, 10, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 35, 51, 0, 51, 15],
    ![0, 35, 0, 34, 0, 51, 51],
    ![0, 51, 34, 0, 0, 8, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 51, 51, 8, 0, 0, 52],
    ![0, 15, 51, 51, 0, 52, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 19, 53, 51, 0, 53],
    ![0, 19, 0, 53, 53, 0, 20],
    ![0, 53, 53, 0, 6, 0, 9],
    ![0, 51, 53, 6, 0, 0, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 53, 20, 9, 53, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 50, 24, 16, 52, 0],
    ![0, 50, 0, 50, 53, 23, 0],
    ![0, 24, 50, 0, 50, 7, 0],
    ![0, 16, 53, 50, 0, 50, 0],
    ![0, 52, 23, 7, 50, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 50, 30, 22, 52],
    ![0, 0, 50, 0, 50, 53, 29],
    ![0, 0, 30, 50, 0, 50, 13],
    ![0, 0, 22, 53, 50, 0, 50],
    ![0, 0, 52, 29, 13, 50, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 52, 35, 19, 50],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![52, 0, 0, 0, 50, 36, 28],
    ![35, 0, 0, 50, 0, 50, 53],
    ![19, 0, 0, 36, 50, 0, 50],
    ![50, 0, 0, 28, 53, 50, 0]],
    ![![0, 0, 53, 0, 51, 53, 24],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 0, 0, 0, 53, 38, 27],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 0, 53, 0, 0, 37, 53],
    ![53, 0, 38, 0, 37, 0, 53],
    ![24, 0, 27, 0, 53, 53, 0]],
    ![![0, 0, 32, 51, 0, 51, 16],
    ![0, 0, 0, 0, 0, 0, 0],
    ![32, 0, 0, 52, 0, 51, 51],
    ![51, 0, 52, 0, 0, 39, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 0, 51, 39, 0, 0, 17],
    ![16, 0, 51, 51, 0, 17, 0]],
    ![![0, 0, 21, 51, 51, 0, 52],
    ![0, 0, 0, 0, 0, 0, 0],
    ![21, 0, 0, 41, 51, 0, 51],
    ![51, 0, 41, 0, 40, 0, 51],
    ![51, 0, 51, 40, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0, 0],
    ![52, 0, 51, 51, 14, 0, 0]],
    ![![0, 0, 53, 26, 15, 53, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 0, 0, 25, 53, 51, 0],
    ![26, 0, 25, 0, 53, 53, 0],
    ![15, 0, 53, 53, 0, 12, 0],
    ![53, 0, 51, 53, 12, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 53, 32, 21, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 53, 0, 0, 31, 53, 51],
    ![0, 32, 0, 31, 0, 53, 53],
    ![0, 21, 0, 53, 53, 0, 18],
    ![0, 53, 0, 51, 53, 18, 0]],
    ![![0, 0, 0, 52, 35, 19, 50],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![52, 0, 0, 0, 50, 36, 28],
    ![35, 0, 0, 50, 0, 50, 53],
    ![19, 0, 0, 36, 50, 0, 50],
    ![50, 0, 0, 28, 53, 50, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 50, 0, 0, 34, 53, 50],
    ![50, 0, 0, 0, 52, 41, 25],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![34, 52, 0, 0, 0, 50, 0],
    ![53, 41, 0, 0, 50, 0, 50],
    ![50, 25, 0, 0, 0, 50, 0]],
    ![![0, 30, 0, 33, 0, 53, 53],
    ![30, 0, 0, 53, 0, 51, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![33, 53, 0, 0, 0, 53, 2],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 51, 0, 53, 0, 0, 1],
    ![53, 53, 0, 2, 0, 1, 0]],
    ![![0, 22, 0, 51, 51, 0, 23],
    ![22, 0, 0, 38, 51, 0, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 38, 0, 0, 52, 0, 51],
    ![51, 51, 0, 52, 0, 0, 3],
    ![0, 0, 0, 0, 0, 0, 0],
    ![23, 51, 0, 51, 3, 0, 0]],
    ![![0, 52, 0, 51, 51, 20, 0],
    ![52, 0, 0, 27, 51, 51, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 27, 0, 0, 5, 51, 0],
    ![51, 51, 0, 5, 0, 4, 0],
    ![20, 51, 0, 51, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 52, 0, 51, 51, 26],
    ![0, 52, 0, 0, 33, 51, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 51, 33, 0, 0, 11, 51],
    ![0, 51, 51, 0, 11, 0, 10],
    ![0, 26, 51, 0, 51, 10, 0]],
    ![![0, 0, 53, 0, 51, 53, 24],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 0, 0, 0, 53, 38, 27],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 0, 53, 0, 0, 37, 53],
    ![53, 0, 38, 0, 37, 0, 53],
    ![24, 0, 27, 0, 53, 53, 0]],
    ![![0, 50, 0, 0, 34, 53, 50],
    ![50, 0, 0, 0, 52, 41, 25],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![34, 52, 0, 0, 0, 50, 0],
    ![53, 41, 0, 0, 50, 0, 50],
    ![50, 25, 0, 0, 0, 50, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 50, 31, 0, 0, 6, 50],
    ![50, 0, 50, 0, 0, 40, 53],
    ![31, 50, 0, 0, 0, 52, 5],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![6, 40, 52, 0, 0, 0, 50],
    ![50, 53, 5, 0, 0, 50, 0]],
    ![![0, 53, 53, 0, 8, 0, 7],
    ![53, 0, 36, 0, 39, 0, 53],
    ![53, 36, 0, 0, 53, 0, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![8, 39, 53, 0, 0, 0, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![7, 53, 51, 0, 53, 0, 0]],
    ![![0, 29, 51, 0, 51, 9, 0],
    ![29, 0, 28, 0, 51, 51, 0],
    ![51, 28, 0, 0, 2, 51, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 51, 2, 0, 0, 52, 0],
    ![9, 51, 51, 0, 52, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 35, 51, 0, 51, 15],
    ![0, 35, 0, 34, 0, 51, 51],
    ![0, 51, 34, 0, 0, 8, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 51, 51, 8, 0, 0, 52],
    ![0, 15, 51, 51, 0, 52, 0]],
    ![![0, 0, 32, 51, 0, 51, 16],
    ![0, 0, 0, 0, 0, 0, 0],
    ![32, 0, 0, 52, 0, 51, 51],
    ![51, 0, 52, 0, 0, 39, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 0, 51, 39, 0, 0, 17],
    ![16, 0, 51, 51, 0, 17, 0]],
    ![![0, 30, 0, 33, 0, 53, 53],
    ![30, 0, 0, 53, 0, 51, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![33, 53, 0, 0, 0, 53, 2],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 51, 0, 53, 0, 0, 1],
    ![53, 53, 0, 2, 0, 1, 0]],
    ![![0, 50, 31, 0, 0, 6, 50],
    ![50, 0, 50, 0, 0, 40, 53],
    ![31, 50, 0, 0, 0, 52, 5],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![6, 40, 52, 0, 0, 0, 50],
    ![50, 53, 5, 0, 0, 50, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 50, 53, 11, 0, 0, 50],
    ![50, 0, 50, 37, 0, 0, 12],
    ![53, 50, 0, 50, 0, 0, 4],
    ![11, 37, 50, 0, 0, 0, 52],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![50, 12, 4, 52, 0, 0, 0]],
    ![![0, 13, 53, 51, 0, 53, 0],
    ![13, 0, 53, 53, 0, 14, 0],
    ![53, 53, 0, 0, 0, 3, 0],
    ![51, 53, 0, 0, 0, 53, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 14, 3, 53, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 19, 53, 51, 0, 53],
    ![0, 19, 0, 53, 53, 0, 20],
    ![0, 53, 53, 0, 6, 0, 9],
    ![0, 51, 53, 6, 0, 0, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 53, 20, 9, 53, 0, 0]],
    ![![0, 0, 21, 51, 51, 0, 52],
    ![0, 0, 0, 0, 0, 0, 0],
    ![21, 0, 0, 41, 51, 0, 51],
    ![51, 0, 41, 0, 40, 0, 51],
    ![51, 0, 51, 40, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0, 0],
    ![52, 0, 51, 51, 14, 0, 0]],
    ![![0, 22, 0, 51, 51, 0, 23],
    ![22, 0, 0, 38, 51, 0, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 38, 0, 0, 52, 0, 51],
    ![51, 51, 0, 52, 0, 0, 3],
    ![0, 0, 0, 0, 0, 0, 0],
    ![23, 51, 0, 51, 3, 0, 0]],
    ![![0, 53, 53, 0, 8, 0, 7],
    ![53, 0, 36, 0, 39, 0, 53],
    ![53, 36, 0, 0, 53, 0, 51],
    ![0, 0, 0, 0, 0, 0, 0],
    ![8, 39, 53, 0, 0, 0, 53],
    ![0, 0, 0, 0, 0, 0, 0],
    ![7, 53, 51, 0, 53, 0, 0]],
    ![![0, 50, 53, 11, 0, 0, 50],
    ![50, 0, 50, 37, 0, 0, 12],
    ![53, 50, 0, 50, 0, 0, 4],
    ![11, 37, 50, 0, 0, 0, 52],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![50, 12, 4, 52, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 50, 18, 10, 52, 0, 0],
    ![50, 0, 50, 53, 17, 0, 0],
    ![18, 50, 0, 50, 1, 0, 0],
    ![10, 53, 50, 0, 50, 0, 0],
    ![52, 17, 1, 50, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]],
    ![![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 50, 24, 16, 52, 0],
    ![0, 50, 0, 50, 53, 23, 0],
    ![0, 24, 50, 0, 50, 7, 0],
    ![0, 16, 53, 50, 0, 50, 0],
    ![0, 52, 23, 7, 50, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 53, 26, 15, 53, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 0, 0, 25, 53, 51, 0],
    ![26, 0, 25, 0, 53, 53, 0],
    ![15, 0, 53, 53, 0, 12, 0],
    ![53, 0, 51, 53, 12, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 52, 0, 51, 51, 20, 0],
    ![52, 0, 0, 27, 51, 51, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 27, 0, 0, 5, 51, 0],
    ![51, 51, 0, 5, 0, 4, 0],
    ![20, 51, 0, 51, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 29, 51, 0, 51, 9, 0],
    ![29, 0, 28, 0, 51, 51, 0],
    ![51, 28, 0, 0, 2, 51, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![51, 51, 2, 0, 0, 52, 0],
    ![9, 51, 51, 0, 52, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 13, 53, 51, 0, 53, 0],
    ![13, 0, 53, 53, 0, 14, 0],
    ![53, 53, 0, 0, 0, 3, 0],
    ![51, 53, 0, 0, 0, 53, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![53, 14, 3, 53, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 50, 18, 10, 52, 0, 0],
    ![50, 0, 50, 53, 17, 0, 0],
    ![18, 50, 0, 50, 1, 0, 0],
    ![10, 53, 50, 0, 50, 0, 0],
    ![52, 17, 1, 50, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0]]]] a b d e

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem certificate_valid : ∀ a b d e : Fin 7, [a,b,d,e].Nodup →
    let t : P := swap a b * swap d e
    let code := (certificate a b d e).val
    if code < 42 then
      t = c ^ (code / 6) * reps ⟨code % 6, Nat.mod_lt _ (by decide)⟩ * (c ^ (code / 6))⁻¹
    else
      let i := (code - 42) / 7
      let j := (code - 42) % 7
      (c ^ i * t * c ^ j * t) ^ 5 = 1 ∧ c ^ i * t * c ^ j * t ≠ 1 := by
  decide +kernel

private theorem calculation (a b d e : Fin 7) (hn : [a,b,d,e].Nodup) :
    let t : P := swap a b * swap d e
    (∃ k : ℕ, ∃ r : Fin 6, t = c ^ k * reps r * (c ^ k)⁻¹) ∨
    ∃ i j : ℕ, (c ^ i * t * c ^ j * t) ^ 5 = 1 ∧ c ^ i * t * c ^ j * t ≠ 1 := by
  have h := certificate_valid a b d e hn
  dsimp only at h ⊢
  split at h
  · exact Or.inl ⟨_, _, h⟩
  · exact Or.inr ⟨_, _, h⟩

private def representativeWord : Fin 6 → List Bool := ![
  [true], [true], [false,false,false,true,false,true,false],
  [false,true,false,true,false,false,false],
  [false,false,true,false,false,false,true,false],
  [false,true,false,false,false,true,false,false]]
private def representativePlane : Fin 6 → Bool := ![false,true,false,true,true,false]

private theorem representative_word : ∀ r : Fin 6,
    involution (representativePlane r) = word cycle (reps r) (representativeWord r) := by
  decide +kernel

private theorem seed_le_of_representative (U : Subgroup P) (hc : cycle ∈ U)
    (r : Fin 6) (hr : reps r ∈ U) : seed (representativePlane r) ≤ U := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact hc
  · have hx' : x = involution (representativePlane r) := Set.mem_singleton_iff.mp hx
    rw [hx', representative_word]
    exact word_mem U hc hr _

private theorem even_involution_double_swap (t : P) (ht : orderOf t = 2)
    (hs : Equiv.Perm.sign t = 1) :
    ∃ a b d e : Fin 7, [a,b,d,e].Nodup ∧ t = swap a b * swap d e := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (ht ▸ Nat.prime_two)
  rw [ht] at hk
  have hb := t.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  rw [Equiv.Perm.sign_of_cycleType', hk] at hs
  have hkbound : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hs
    · rfl
    · norm_num at hs
  have hct : t.cycleType = {2,2} := by simpa [hk1] using hk
  have hbase : (involution false).cycleType = {2,2} :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq (hbase.trans hct.symm))
  refine ⟨g 2, g 3, g 4, g 6, ?_, ?_⟩
  · exact List.Nodup.map g.injective (by decide : ([2,3,4,6] : List (Fin 7)).Nodup)
  · rw [← hg]
    change g * (swap 2 3 * swap 4 6) * g⁻¹ = _
    rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    group

set_option maxHeartbeats 400000 in
/-- A subgroup of order 168 containing the seven-cycle and an even involution
contains one of the two explicit binary-plane groups. -/
public theorem seed_le_of_even_involution (U : Subgroup Perm) (hc : cycle ∈ U)
    (hcard : Nat.card U = 168) (t : U) (ht : orderOf t = 2)
    (hs : Equiv.Perm.sign (t : Perm) = 1) : ∃ b : Bool, seed b ≤ U := by
  obtain ⟨a,b,d,e, hn, he⟩ := even_involution_double_swap t
    ((Subgroup.orderOf_coe t).trans ht) hs
  rcases calculation a b d e hn with ⟨k,r,hr⟩ | ⟨i,j, hw, hne⟩
  · have hrep : reps r ∈ U := by
      have hr' : reps r = (cycle ^ k)⁻¹ * (t : P) * cycle ^ k := by
        rw [he, hr]
        group
      rw [hr']
      exact U.mul_mem (U.mul_mem (U.inv_mem (U.pow_mem hc k)) t.property) (U.pow_mem hc k)
    exact ⟨_, seed_le_of_representative U hc r hrep⟩
  · let w : U := ⟨cycle ^ i * t * cycle ^ j * t,
      U.mul_mem (U.mul_mem (U.mul_mem (U.pow_mem hc i) t.property)
        (U.pow_mem hc j)) t.property⟩
    have hp : w ^ 5 = 1 := by
      apply Subtype.ext
      change (cycle ^ i * (t : P) * cycle ^ j * t) ^ 5 = 1
      simpa only [he] using hw
    have hnw : w ≠ 1 := by
      intro h
      apply hne
      have hval := congrArg Subtype.val h
      change cycle ^ i * (t : P) * cycle ^ j * t = 1 at hval
      simpa only [he] using hval
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have ho : orderOf w = 5 := orderOf_eq_prime hp hnw
    have hd := orderOf_dvd_natCard w
    rw [ho, hcard] at hd
    norm_num at hd

end CFSG.Quasithin.MainConverse.Order168Recognition
