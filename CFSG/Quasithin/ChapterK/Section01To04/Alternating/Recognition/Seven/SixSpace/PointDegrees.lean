module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.Inputs
public import Theory.Representation.BinaryAlternatingSixSmallDegrees

/-!
# Binary simple degrees for the literal A₇ point stabilizer

Restrict permutations to the six letters complementary to zero, and label that
complement to obtain an actual isomorphism with A₆. Pulling a representation
back along this isomorphism preserves its invariant-subspace lattice and its
vector space. The elementary A₆ orbit-counting theorem therefore proves the
required degree gap without a faithfulness or cubic-action assumption.

This discharges the degree input used by `SevenSixSpace.fixed_or_dual` and
`sevenSixSpace_of_pointSimpleDegrees`. Source purpose: Aschbacher–Smith K.1.2,
printed p.452 (PDF p.463), the recognition of the A₇ six-dimensional module.
The proof uses no representation catalogue or Chapter B classification.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
universe v

/-- The literal point stabilizer has only binary simple degrees one and four
through dimension six, including representations with nontrivial kernel. -/
theorem pointSimpleDegrees : PointSimpleDegrees.{v} := by
  intro W _ _ _ σ hσ hd
  let e : PointStabilizer ≃* alternatingGroup (Fin 6) :=
    AlternatingSix.SmallIndex.pointEquiv (0 : Fin 7)
  let τ : Representation (ZMod 2) (alternatingGroup (Fin 6)) W :=
    σ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible := hσ
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr hσ
  exact AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four τ hd

end CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
