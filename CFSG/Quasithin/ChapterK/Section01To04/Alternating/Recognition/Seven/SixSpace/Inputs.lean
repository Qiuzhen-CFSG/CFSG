module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants

/-!
# The point-stabilizer degree input for the A₇ six-space

The stabilizer of one of the seven letters is the literal subgroup used in
restriction and in the orbit-map construction. Its binary simple degrees up to
six suffice for recognition: a simple quotient of a six-space has degree one
or four, and in the latter case the two-dimensional kernel has a fixed line.
This records the remaining degree obligation, without asserting its proof or
assuming any equivalence with the desired A₇ module.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463), citing GM02
Theorem 6.2 and Table 6.3. This is a sufficient point-stabilizer route to the
six-dimensional row, independent of the ambient cubic degree bound.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace

/-- The actor with its original seven-letter marking. -/
abbrev Actor := alternatingGroup (Fin 7)

/-- The actual stabilizer of letter zero, isomorphic to A₆. -/
abbrev PointStabilizer := MulAction.stabilizer Actor (0 : Fin 7)

universe v

/-- The binary simple-degree gap needed only through dimension six.
This proposition is a proof obligation, not an established catalogue. -/
def PointSimpleDegrees : Prop :=
  ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) PointStabilizer W),
    σ.IsIrreducible → Module.finrank (ZMod 2) W ≤ 6 →
      Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 4

end CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
