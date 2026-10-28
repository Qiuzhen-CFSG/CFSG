module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# Explicit relators for the local quotient certificate

These 47 words were obtained experimentally from GAP's
`IsomorphismFpGroupByGenerators` on the degree-24 point maps for left
conjugation by the ATLAS `J4G1-max1W1` local generators. This module only
specifies words; it asserts neither the correctness of GAP's presentation nor
its order. The two independent obligations are to bound this presented group
and to evaluate its relators inside the actual matrix subgroup.

The generators are `false = x` and `true = y`. In each signed letter the
second Boolean is true for a generator and false for its inverse. GAP words
have been reversed because GAP permutation multiplication is opposite Lean
composition. The original witnesses and generation scripts are retained in
the adjacent `source/` directory. Source of the local
generators: the ATLAS `J4G1-max1W1` program cited in `Cardinality.Subgroup`.
-/

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.UpperBound

local notation "x" => ((false, true) : Bool × Bool)
local notation "xi" => ((false, false) : Bool × Bool)
local notation "y" => ((true, true) : Bool × Bool)
local notation "yi" => ((true, false) : Bool × Bool)

/-- Relator 0, in Lean multiplication order. -/
def relatorLetters0 : List (Bool × Bool) :=
  [x, x]

/-- Relator 1, in Lean multiplication order. -/
def relatorLetters1 : List (Bool × Bool) :=
  [y, y, y]

/-- Relator 2, in Lean multiplication order. -/
def relatorLetters2 : List (Bool × Bool) :=
  [y, x, y, x, y, x, y, x, y, x, y, x, y, x, y, x, y, x, y, x, y, x, y, x,
   y, x, y, x]

/-- Relator 3, in Lean multiplication order. -/
def relatorLetters3 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x]

/-- Relator 4, in Lean multiplication order. -/
def relatorLetters4 : List (Bool × Bool) :=
  [yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x]

/-- Relator 5, in Lean multiplication order. -/
def relatorLetters5 : List (Bool × Bool) :=
  [x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi,
   x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y]

/-- Relator 6, in Lean multiplication order. -/
def relatorLetters6 : List (Bool × Bool) :=
  [x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y]

/-- Relator 7, in Lean multiplication order. -/
def relatorLetters7 : List (Bool × Bool) :=
  [yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x]

/-- Relator 8, in Lean multiplication order. -/
def relatorLetters8 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y]

/-- Relator 9, in Lean multiplication order. -/
def relatorLetters9 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x]

/-- Relator 10, in Lean multiplication order. -/
def relatorLetters10 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x]

/-- Relator 11, in Lean multiplication order. -/
def relatorLetters11 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x]

/-- Relator 12, in Lean multiplication order. -/
def relatorLetters12 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, y, x]

/-- Relator 13, in Lean multiplication order. -/
def relatorLetters13 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, y]

/-- Relator 14, in Lean multiplication order. -/
def relatorLetters14 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, y, x, y]

/-- Relator 15, in Lean multiplication order. -/
def relatorLetters15 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- Relator 16, in Lean multiplication order. -/
def relatorLetters16 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- Relator 17, in Lean multiplication order. -/
def relatorLetters17 : List (Bool × Bool) :=
  [y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x]

/-- Relator 18, in Lean multiplication order. -/
def relatorLetters18 : List (Bool × Bool) :=
  [y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x]

/-- Relator 19, in Lean multiplication order. -/
def relatorLetters19 : List (Bool × Bool) :=
  [yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x]

/-- Relator 20, in Lean multiplication order. -/
def relatorLetters20 : List (Bool × Bool) :=
  [yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x]

/-- Relator 21, in Lean multiplication order. -/
def relatorLetters21 : List (Bool × Bool) :=
  [y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, y, x, yi, x]

/-- Relator 22, in Lean multiplication order. -/
def relatorLetters22 : List (Bool × Bool) :=
  [x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y]

/-- Relator 23, in Lean multiplication order. -/
def relatorLetters23 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi]

/-- Relator 24, in Lean multiplication order. -/
def relatorLetters24 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y]

/-- Relator 25, in Lean multiplication order. -/
def relatorLetters25 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x]

/-- Relator 26, in Lean multiplication order. -/
def relatorLetters26 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   y, x, yi, x, yi, x, y, x]

/-- Relator 27, in Lean multiplication order. -/
def relatorLetters27 : List (Bool × Bool) :=
  [yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, yi, x, y, x, yi, x, y, x]

/-- Relator 28, in Lean multiplication order. -/
def relatorLetters28 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, y, x, y, x, yi]

/-- Relator 29, in Lean multiplication order. -/
def relatorLetters29 : List (Bool × Bool) :=
  [yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x]

/-- Relator 30, in Lean multiplication order. -/
def relatorLetters30 : List (Bool × Bool) :=
  [yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x]

/-- Relator 31, in Lean multiplication order. -/
def relatorLetters31 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi]

/-- Relator 32, in Lean multiplication order. -/
def relatorLetters32 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- Relator 33, in Lean multiplication order. -/
def relatorLetters33 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x]

/-- Relator 34, in Lean multiplication order. -/
def relatorLetters34 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y]

/-- Relator 35, in Lean multiplication order. -/
def relatorLetters35 : List (Bool × Bool) :=
  [yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x]

/-- Relator 36, in Lean multiplication order. -/
def relatorLetters36 : List (Bool × Bool) :=
  [y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x]

/-- Relator 37, in Lean multiplication order. -/
def relatorLetters37 : List (Bool × Bool) :=
  [yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- Relator 38, in Lean multiplication order. -/
def relatorLetters38 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y]

/-- Relator 39, in Lean multiplication order. -/
def relatorLetters39 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x]

/-- Relator 40, in Lean multiplication order. -/
def relatorLetters40 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi,
   x, y]

/-- Relator 41, in Lean multiplication order. -/
def relatorLetters41 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y]

/-- Relator 42, in Lean multiplication order. -/
def relatorLetters42 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y]

/-- Relator 43, in Lean multiplication order. -/
def relatorLetters43 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y]

/-- Relator 44, in Lean multiplication order. -/
def relatorLetters44 : List (Bool × Bool) :=
  [y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x]

/-- Relator 45, in Lean multiplication order. -/
def relatorLetters45 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x,
   y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x,
   y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- Relator 46, in Lean multiplication order. -/
def relatorLetters46 : List (Bool × Bool) :=
  [yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x,
   y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x,
   y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x,
   y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x,
   yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x]

/-- The complete family of signed words. -/
def relatorLetters (i : Fin 47) : List (Bool × Bool) :=
  Vector.get #v[relatorLetters0, relatorLetters1, relatorLetters2, relatorLetters3, relatorLetters4, relatorLetters5, relatorLetters6, relatorLetters7, relatorLetters8, relatorLetters9, relatorLetters10, relatorLetters11, relatorLetters12, relatorLetters13, relatorLetters14, relatorLetters15, relatorLetters16, relatorLetters17, relatorLetters18, relatorLetters19, relatorLetters20, relatorLetters21, relatorLetters22, relatorLetters23, relatorLetters24, relatorLetters25, relatorLetters26, relatorLetters27, relatorLetters28, relatorLetters29, relatorLetters30, relatorLetters31, relatorLetters32, relatorLetters33, relatorLetters34, relatorLetters35, relatorLetters36, relatorLetters37, relatorLetters38, relatorLetters39, relatorLetters40, relatorLetters41, relatorLetters42, relatorLetters43, relatorLetters44, relatorLetters45, relatorLetters46] i

/-- These words as elements of the free group on the two local generators. -/
def relatorWord (i : Fin 47) : FreeGroup Bool := FreeGroup.mk (relatorLetters i)

/-- An explicit candidate presentation; its size is a separate proof obligation. -/
abbrev Presentation := PresentedGroup (Set.range relatorWord)

/-- Proposed binary-product masks, to be certified by matrix evaluation. -/
def relatorMask (i : Fin 47) : Nat :=
  Vector.get #v[0, 0, 2, 1348, 1018, 1366, 1485, 1166, 784, 901, 1301, 1388, 1154, 1105, 0, 411, 1969, 1184, 1991, 1465, 576, 1625, 1809, 272, 573, 891, 1647, 456, 809, 1020, 1631, 2005, 1120, 319, 24, 1556, 1600, 926, 180, 450, 1778, 1340, 716, 868, 390, 1642, 1894] i

end Janko4.Cardinality.QuotientCount.UpperBound
