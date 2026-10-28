module

public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.GroupTheory.PrimeRankCentralCover


/-!
# Automorphism two-rank of the actual special unitary cover

The special-to-projective map has kernel equal to the whole center, and
SU₃(2ⁿ) is perfect for n ≥ 2. Hence automorphism descent is injective. The
proved projective automorphism bound gives the same bound n+1 for SU₃.
The cover is retained even when its scalar center is nontrivial.

The model's perfectness is proved from the given field data; it is not an
additional hypothesis. Source: GLS4, Chapter 4, Lemma 3.5(b), as used for
the unitary covers in Chapter 2, Section 13.
-/

public section

open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank

/-- Faithful descent bounds the automorphisms of SU₃(2ⁿ) by n+1. -/
theorem special_automorphism_two_rank_le {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    primeRank 2 (MulAut J.specialSubgroup) ≤ n + 1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  let f : PerfectCentralCovering.Cover J.specialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := J.specialToProjective
    surjective := J.specialToProjective_surjective
    isPerfect := Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hn hcard hconj
    ker_le_center := J.specialToProjective_ker_le_center }
  have hk := J.specialToProjective_ker_eq_center
    (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  exact (f.automorphism_primeRank_le hk 2).trans
    (automorphism_two_rank_le J hn hcard hconj)

end BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
