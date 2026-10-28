module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.Fin.VecNotation

/-!
# Candidate relators for the max2 quotient

These 29 words were discovered by GAP on the saved twelve-dimensional binary
right-conjugation matrices. GAP first converts the matrix group to a degree-693
permutation image, then calls `IsomorphismFpGroupByGenerators` on the images of
the same ordered generators. The words retain matrix multiplication order.
No correctness, finiteness or order of the candidate presentation is asserted.

The independent proof obligations are a finite upper bound for this presented
group and membership of the lifted relators in the actual normal closure.
The adjacent `source/` files preserve the untrusted discovery and masks.
The original max2 generators come from ATLAS `J4G1-max2W1`; see `Max2Bridge`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation

local notation "x" => ((false, true) : Bool × Bool)
local notation "xi" => ((false, false) : Bool × Bool)
local notation "y" => ((true, true) : Bool × Bool)
local notation "yi" => ((true, false) : Bool × Bool)

def relatorLetters0 : List (Bool × Bool) :=
  [x, x]

def relatorLetters1 : List (Bool × Bool) :=
  [y, y, y]

def relatorLetters2 : List (Bool × Bool) :=
  [x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, yi, x, yi]

def relatorLetters3 : List (Bool × Bool) :=
  [x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y]

def relatorLetters4 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi]

def relatorLetters5 : List (Bool × Bool) :=
  [y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x,
   y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x]

def relatorLetters6 : List (Bool × Bool) :=
  [x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y]

def relatorLetters7 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y]

def relatorLetters8 : List (Bool × Bool) :=
  [x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, y]

def relatorLetters9 : List (Bool × Bool) :=
  [x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi]

def relatorLetters10 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y,
   x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y]

def relatorLetters11 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, yi]

def relatorLetters12 : List (Bool × Bool) :=
  [x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, y, x, y, x, y, x, y, x, y, x, yi]

def relatorLetters13 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi]

def relatorLetters14 : List (Bool × Bool) :=
  [y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x,
   y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x,
   yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x]

def relatorLetters15 : List (Bool × Bool) :=
  [x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, y]

def relatorLetters16 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi,
   x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi]

def relatorLetters17 : List (Bool × Bool) :=
  [x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y]

def relatorLetters18 : List (Bool × Bool) :=
  [y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y, x,
   yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x,
   yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x,
   y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x,
   yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x,
   y, x, yi, x, y, x, yi, x]

def relatorLetters19 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, y,
   x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, y]

def relatorLetters20 : List (Bool × Bool) :=
  [y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x,
   yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x,
   yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x,
   y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x,
   y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x,
   y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x,
   yi, x, yi, x, y, x, yi, x]

def relatorLetters21 : List (Bool × Bool) :=
  [x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi]

def relatorLetters22 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi]

def relatorLetters23 : List (Bool × Bool) :=
  [x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi,
   x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi]

def relatorLetters24 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi,
   x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y,
   x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, yi, x, y, x, yi, x, yi]

def relatorLetters25 : List (Bool × Bool) :=
  [x, y, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, yi, x, yi,
   x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi,
   x, y, x, yi, x, y, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, yi, x, y,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, yi]

def relatorLetters26 : List (Bool × Bool) :=
  [x, y, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi,
   x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, y, x, yi, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, y,
   x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, y,
   x, y, x, y, x, yi, x, y, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y]

def relatorLetters27 : List (Bool × Bool) :=
  [x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi,
   x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y,
   x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, y,
   x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y,
   x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, yi, x, y, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi,
   x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi]

def relatorLetters28 : List (Bool × Bool) :=
  [x, yi, x, y, x, y, x, y, x, y, x, y, x, y, x, yi, x, y, x, y, x, y, x, y,
   x, y, x, yi, x, y, x, yi, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi,
   x, y, x, y, x, yi, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, y, x, yi, x, yi,
   x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, y, x, yi, x, yi, x, yi,
   x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi, x, y, x, yi, x, yi, x, yi, x, yi,
   x, y, x, y, x, yi, x, yi, x, y, x, y, x, yi, x, y, x, yi, x, y, x, yi, x, y,
   x, yi, x, y, x, y, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y,
   x, yi, x, y, x, yi, x, yi, x, yi, x, y, x, y, x, y, x, y, x, y, x, yi, x, y]

def relatorLetters : Fin 29 → List (Bool × Bool) :=
  ![relatorLetters0, relatorLetters1, relatorLetters2, relatorLetters3, relatorLetters4, relatorLetters5, relatorLetters6, relatorLetters7, relatorLetters8, relatorLetters9, relatorLetters10, relatorLetters11, relatorLetters12, relatorLetters13, relatorLetters14, relatorLetters15, relatorLetters16, relatorLetters17, relatorLetters18, relatorLetters19, relatorLetters20, relatorLetters21, relatorLetters22, relatorLetters23, relatorLetters24, relatorLetters25, relatorLetters26, relatorLetters27, relatorLetters28]

def relatorWord (i : Fin 29) : FreeGroup Bool := FreeGroup.mk (relatorLetters i)

def relatorMask : Fin 29 → ℕ :=
  ![0, 0, 0, 3699, 13, 2994, 7610, 5823, 7695, 5717, 2678, 4600, 4241, 3150, 5867, 1673, 1001, 7450, 3967, 195, 8110, 2829, 6079, 3182, 551, 7004, 4784, 2759, 3550]

abbrev Group := PresentedGroup (Set.range relatorWord)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation
