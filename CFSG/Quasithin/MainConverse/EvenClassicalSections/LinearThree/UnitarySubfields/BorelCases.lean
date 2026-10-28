module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# The Sylow-overgroup branch of unitary subgroup exhaustion

The proved matrix root-generation theorem places every proper overgroup
of a Sylow 2-subgroup inside its solvable Borel normalizer. This supplies
an intrinsic solvable branch of the pending subgroup exhaustion, for
arbitrary allowed Hermitian forms and every positive fixed-field exponent.

Source: Aschbacher–Smith, F.1.3(1), printed pp.259–260; the unitary
parabolic case of Hartley–Mitchell in GLS3, Theorem 6.5.3(a).
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections

open BenderSuzuki.MatrixGroups

/-- Proper Sylow overgroups lie inside a solvable unitary Borel. -/
public theorem psu3_matrix_solvable_of_sylow_le
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : U ≠ ⊤) (hTU : (T : Subgroup _) ≤ U) : Group.IsSolvable U := by
  have h := ChapterF.Source.rankOneSylowFacts_psu3 J n hn hcard hconj T
  let := h.solvable
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (h.unique_maximal U hTU (lt_top_iff_ne_top.mpr hU)))

/-- The intrinsic root-generation result closes this branch of the envelope. -/
public theorem Envelope.of_sylow_le
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : U ≠ ⊤) (hTU : (T : Subgroup _) ≤ U) : Envelope n U :=
  .solvable U (psu3_matrix_solvable_of_sylow_le J hn hcard hconj T U hU hTU)

end CFSG.Quasithin.MainConverse.UnitaryThreeSections
