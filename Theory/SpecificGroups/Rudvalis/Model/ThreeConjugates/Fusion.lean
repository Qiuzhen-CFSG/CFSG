module

public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.FusionChecks
public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.FusionRoots
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.NormalFormCoverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Every Rudvalis involution is conjugate to a marked representative

The word-defined candidate has order 2^14 and odd index in the actual model,
so every involution has a conjugate in it. Its complete binary normal forms
are covered by the checked forest: square obstructions exclude non-involutions,
and strict descent reaches one of the fifteen roots. Checked ambient words
fuse each root to `a` or `b²`.

This is element coverage, independent of centralizer classification and
automorphism innerness. It supplies the universal quantifier in the Rudvalis
case of Revin–Zavarnitsine, arXiv:2505.05173v2, Theorem 1. The ATLAS source
and action convention are documented in `Model.PermutationData`.
-/

namespace Rudvalis.ThreeConjugates
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open FusionCertificate

private theorem normal_zero : candidateNormalForm 0 = 1 := by
  simp [candidateNormalForm]

private theorem normal_form_fusion (n : Fin 16384)
    (hne : candidateNormalForm n ≠ 1) (hsq : candidateNormalForm n ^ 2 = 1) :
    IsConj (candidateNormalForm n) a ∨ IsConj (candidateNormalForm n) (b^2) := by
  have aux (k : Nat) : ∀ n : Fin 16384, height n = k →
      candidateNormalForm n ≠ 1 → candidateNormalForm n ^ 2 = 1 →
      IsConj (candidateNormalForm n) a ∨ IsConj (candidateNormalForm n) (b^2) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hn hne hsq
      rcases tests n with hzero | hbad | hroot | ⟨hheight, hpoints⟩
      · subst n
        exact (hne normal_zero).elim
      · apply (hbad _).elim
        have he := congrArg (fun g : Model => g • obstruction n) hsq
        simpa only [pow_two, mul_smul, normal_smul, one_smul] using he
      · exact root_fusion n hroot
      · have he : candidateNormalForm n * candidateGenerator (letter n) =
            candidateGenerator (letter n) * candidateNormalForm (parent n) := by
          apply eq_of_smul_first_five
          intro i
          simpa only [mul_smul, normal_smul, generator_smul] using hpoints i
        have hc : IsConj (candidateNormalForm (parent n)) (candidateNormalForm n) :=
          isConj_iff.mpr ⟨candidateGenerator (letter n),
            mul_inv_eq_iff_eq_mul.mpr he.symm⟩
        have hpne : candidateNormalForm (parent n) ≠ 1 := by
          intro hp
          rw [hp] at hc
          exact hne (isConj_one_right.mp hc)
        have hpsq : candidateNormalForm (parent n) ^ 2 = 1 := by
          have hp := hc.pow 2
          rw [hsq] at hp
          exact isConj_one_left.mp hp
        have hp := ih (height (parent n)) (hn ▸ hheight) (parent n) rfl hpne hpsq
        exact hp.imp (fun h => hc.symm.trans h) (fun h => hc.symm.trans h)
  exact aux (height n) n rfl hne hsq

/-- The complete normal forms cover every involution in the actual Sylow candidate. -/
public theorem candidate_involution_fusion (t : Model) (ht : t ∈ candidate)
    (hne : t ≠ 1) (hsq : t^2 = 1) : IsConj t a ∨ IsConj t (b^2) := by
  obtain ⟨n, rfl⟩ := exists_candidateNormalForm ht
  exact normal_form_fusion n hne hsq

private theorem candidate_odd_index : ¬ 2 ∣ candidate.index := by
  intro h
  apply not_two_pow_fifteen_dvd_card_model
  rw [← candidate.card_mul_index, candidate_card]
  exact Nat.mul_dvd_mul_left 16384 h

end Rudvalis.ThreeConjugates

namespace Rudvalis
open SylowOvergroups.RadicalCoverage.SylowCertificate

/-- Every involution of the literal degree-4060 model is conjugate to `a` or `b²`. -/
public theorem involution_isConj_a_or_b_sq (t : Model) (ht : orderOf t = 2) :
    IsConj t a ∨ IsConj t (b^2) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 Model :=
    LocalOrder.candidate_isTwoGroup.toSylow ThreeConjugates.candidate_odd_index
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ht)
  have htne : t ≠ 1 := by
    intro he
    rw [he, orderOf_one] at ht
    contradiction
  have htsq : t^2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hyne : (y : Model) ≠ 1 := by
    intro he
    rw [he] at hy
    exact htne (isConj_one_left.mp hy)
  have hysq : (y : Model)^2 = 1 := by
    have hp := hy.pow 2
    rw [htsq] at hp
    exact isConj_one_right.mp hp
  have hf := ThreeConjugates.candidate_involution_fusion y y.property hyne hysq
  exact hf.imp (fun h => hy.trans h) (fun h => hy.trans h)

end Rudvalis
