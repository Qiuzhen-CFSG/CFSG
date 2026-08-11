import ChallengeDeps
import Submission.Helpers
import Submission.BenderSuzuki.FinalTheorem

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-! The benchmark declarations and the repository's final-theorem declarations
use separate namespaces.  The underlying definitions are equivalent, but the
two strong-embedding predicates use parity and involutions respectively. -/

private theorem even_natCard_iff_exists_involution (K : Type*) [Group K] [Finite K] :
    Even (Nat.card K) ↔ ∃ x : K, x ≠ 1 ∧ x ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h.two_dvd
    refine ⟨x, ?_, ?_⟩
    · intro hx1
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by decide)
    · rw [← hx]
      exact pow_orderOf_eq_one x
  · rintro ⟨x, hx1, hx2⟩
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hdiv : (2 : ℕ) ∣ Nat.card K := hord ▸ orderOf_dvd_natCard x
    exact even_iff_two_dvd.mpr hdiv

private theorem even_natCard_subgroup_iff_exists_involution
    {X : Type*} [Group X] [Finite X] (M : Subgroup X) :
    Even (Nat.card M) ↔ ∃ x ∈ M, _root_.BSIsInvolution x := by
  rw [even_natCard_iff_exists_involution]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨(x : X), x.2, ?_, ?_⟩
    · simpa [OneMemClass.coe_eq_one] using hx1
    · have h := congrArg Subtype.val hx2
      simpa using h
  · rintro ⟨x, hxM, hx1, hx2⟩
    refine ⟨⟨x, hxM⟩, ?_, ?_⟩
    · simpa [OneMemClass.coe_eq_one] using hx1
    · apply Subtype.ext
      simpa using hx2

private theorem odd_natCard_subgroup_iff_forall_not_involution
    {X : Type*} [Group X] [Finite X] (M : Subgroup X) :
    Odd (Nat.card M) ↔ ∀ x ∈ M, ¬ _root_.BSIsInvolution x := by
  rw [← Nat.not_even_iff_odd, even_natCard_subgroup_iff_exists_involution]
  constructor
  · intro h x hxM hx
    exact h ⟨x, hxM, hx.1, hx.2⟩
  · rintro h ⟨x, hxM, hx1, hx2⟩
    exact h x hxM ⟨hx1, hx2⟩

private theorem challenge_stronglyEmbedded_to_root
    {X : Type*} [Group X] [Finite X] (M : Subgroup X)
    (h : LeanEval.GroupTheory.Defs.IsStronglyEmbedded M) :
    _root_.BSIsStronglyEmbedded M := by
  refine ⟨h.1, (even_natCard_subgroup_iff_exists_involution M).1 h.2.1, ?_⟩
  intro g hg x hx
  exact (odd_natCard_subgroup_iff_forall_not_involution
    (M ⊓ M.map (MulAut.conj g).toMonoidHom)).1 (h.2.2 g hg) x hx

private theorem root_szModel_eq_challenge (n : ℕ) :
    _root_.BSSzModel n = LeanEval.GroupTheory.Defs.SzModel n := by
  rfl

private theorem root_psu3Model_eq_challenge (n : ℕ) :
    _root_.BSPSU3Model n = LeanEval.GroupTheory.Defs.PSU3Model n := by
  rfl

theorem bender_suzuki {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : LeanEval.GroupTheory.Defs.IsStronglyEmbedded M) :
    LeanEval.GroupTheory.Defs.IsSimpleBenderGroup X := by
  have hroot : _root_.BSIsStronglyEmbedded M :=
    challenge_stronglyEmbedded_to_root M h
  have hclassification : _root_.BSIsSimpleBenderGroup X :=
    _root_.bender_suzuki_internal M hroot
  cases hclassification with
  | isPSL2 n hn e =>
      exact LeanEval.GroupTheory.Defs.IsSimpleBenderGroup.isPSL2 n hn e
  | isSuzuki n hn e =>
      exact LeanEval.GroupTheory.Defs.IsSimpleBenderGroup.isSuzuki n hn
        (e.trans (MulEquiv.subgroupCongr (root_szModel_eq_challenge n)))
  | isPSU3 n hn e =>
      exact LeanEval.GroupTheory.Defs.IsSimpleBenderGroup.isPSU3 n hn
        (e.trans (MulEquiv.subgroupCongr (root_psu3Model_eq_challenge n)))

end Submission
