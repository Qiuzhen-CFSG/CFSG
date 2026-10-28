module

public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The Schur-field branch of the binary SU₃ degree bound

For an irreducible binary action of SU₃(2ˢ) with central kernel, the full
linear normalizer has two-rank at most s+1. Perfect central-cover descent
identifies the central quotient of the action image with the actual PSU₃
carrier, and Schur's lemma makes conjugation faithful on elementary actors.
An actor which moves the Schur field moves at least half of V. If its fixed
codimension is at most twice its rank, this gives dim V ≤ 4(s+1).

No natural-module identification, faithful pullback, or SQTK hypothesis on
the normalizer is required. The source application is in Chapter K's
UnitaryRecognition.CubicDegree.Reduction.

Sources: Aschbacher--Smith, printed pp.451, 456; Guralnick--Malle,
Classification of 2F-modules II, §3.5 and Proposition 4.11.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Subgroup Theory.GroupTheory
namespace Representation.SU3.CubicDegree
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
  (σ : Representation (ZMod 2) J.specialSubgroup V)
  (hi : σ.IsIrreducible) (hk : σ.ker ≤ center J.specialSubgroup)

include hs hcard hconj hi hk

/-- The full normalizer has two-rank at most `s+1`, even for a central-kernel action. -/
theorem normalizer_two_rank_le : primeRank 2 (linearNormalizer σ) ≤ s + 1 := by
  let : Group.IsPerfect J.specialSubgroup :=
    Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hs hcard hconj
  let : Group.IsPerfect (actionImage σ) :=
    Group.IsPerfect.ofSurjective σ.asGroupHom.rangeRestrict_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hz := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  let e : actionImage σ ⧸ center (actionImage σ) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (simpleQuotientEquivImage σ hk).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
          J.specialToProjective_surjective))
  have hq := automorphism_primeRank_le_quotient_center (E := actionImage σ) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hq
  exact (primeRank_linearNormalizer_le σ hi).trans (hq.trans
    (HermitianForm.EvenTwoRank.automorphism_two_rank_le J hs hcard hconj))

/-- The bound applies to every actual elementary actor in the normalizer. -/
theorem elementary_rank_le (A : Subgroup (linearNormalizer σ))
    (hA : IsElementaryTwo A) : rank A ≤ s + 1 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hc := (primeRank_le_iff_elementary_card_le (linearNormalizer σ)).mp
    (normalizer_two_rank_le J hs hcard hconj σ hi hk) A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

/-- A 2F actor moving the Schur field gives degree at most `4*(s+1)`. -/
theorem finrank_le_four_mul_of_not_schurLinear
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (t : linearNormalizer σ) (ht : t ∈ A)
    (hnl : ¬ SchurNormalizer.IsSchurLinear σ t) :
    Module.finrank (ZMod 2) V ≤ 4 * (s + 1) := by
  let : σ.IsIrreducible := hi
  have hd := SchurNormalizer.finrank_le_twice_fixedCodim σ t hnl
  have hf : fixedSpace (normalizerRepresentation σ) A ≤
      fixedSpace (normalizerRepresentation σ) (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hm := Submodule.finrank_mono hf
  have h₁ := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have h₂ := fixedCodim_add_finrank (normalizerRepresentation σ) (zpowers t)
  have hr := elementary_rank_le J hs hcard hconj σ hi hk A hA
  omega

end Representation.SU3.CubicDegree
