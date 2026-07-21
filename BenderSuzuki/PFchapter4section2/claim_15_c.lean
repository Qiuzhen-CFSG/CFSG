/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFchapter4section2.Basic

namespace BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (15)(c) -/

public theorem claim_15_c
    (G E : Type*) [Group G] [Field E] [Finite E] (Q0 KW : Subgroup G) (omega : G)
    (omegaCoord : E → G) (f : G → G)
    (m : ℕ) (zeta alpha beta x : E)
    (tau : E → E) (u d : ℕ → E)
    (sigma : E → E) (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hsequence_orbit : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
        f (omegaCoord (u i)) = rightConjugateElem omega d * q0)
    (hsequence_distinct : ∀ i j : ℕ,
      1 ≤ i → i ≤ m - 1 → 1 ≤ j → j ≤ m - 1 → u i = u j → i = j)
    (horbit_count :
      Nat.card {y : E // (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
        f (omegaCoord y) = rightConjugateElem omega d * q0)} = m - 1) :
    (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧ f (omegaCoord x) = rightConjugateElem omega d * q0) →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ m - 1 ∧ x = u i := by
  classical
  have _ := hseq_zeta_ne_one
  have _ := hseq_alpha_ne_zero
  have _ := hseq_beta_ne_zero
  have _ := hseq_tau_nonzero
  have _ := hseq_zeta_order
  have _ := hseq_recurrence_u
  have _ := hseq_recurrence_d
  have _ := hseq_beta_characteristic_root
  intro hx
  let S : Type _ := {y : E // (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧ f (omegaCoord y) = rightConjugateElem omega d * q0)}
  let F : Fin (m - 1) → S := fun i =>
    ⟨u (i.1 + 1), hsequence_orbit (i.1 + 1) (by omega) (by omega)⟩
  by_contra hcover
  have hF_inj : Function.Injective F := by
    intro a b hab
    apply Fin.ext
    apply Nat.succ.inj
    exact
      hsequence_distinct (a.1 + 1) (b.1 + 1)
        (by omega) (by omega) (by omega) (by omega)
        (congrArg Subtype.val hab)
  have hx_not_range : (⟨x, hx⟩ : S) ∉ Set.range F := by
    rintro ⟨i, hi⟩
    apply hcover
    refine ⟨i.1 + 1, by omega, by omega, ?_⟩
    exact (congrArg Subtype.val hi).symm
  letI : Fintype S := Fintype.ofFinite S
  have hlt : Fintype.card (Fin (m - 1)) < Fintype.card S :=
    Fintype.card_lt_of_injective_of_notMem F hF_inj hx_not_range
  have hcardS : Fintype.card S = m - 1 := by
    rw [Fintype.card_eq_nat_card]
    simpa [S] using horbit_count
  rw [Fintype.card_fin, hcardS] at hlt
  exact (Nat.lt_irrefl (m - 1)) hlt

end PFchapter4section2
end BenderSuzuki

