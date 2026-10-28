module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs

/-!
# The literal involution fibers for J.2.6

These fibers use the actual surjection H → S₅ supplied by Ru2. They retain
an element of H and its ambient order, so subsequent counting and conjugation
arguments use the same lifts as the source statement.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The involutions above one element of the literal H/Q marking. -/
def involutionFiber (d : TypeRuSetup G) (t : S5) : Set d.H :=
  {x | orderOf (x : G) = 2 ∧ d.ru2.quotientMap x = t}

end CFSG.Quasithin.ChapterJ.Fusion.Outer
