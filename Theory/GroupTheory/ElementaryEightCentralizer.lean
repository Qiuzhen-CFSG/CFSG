module

public import Theory.GroupTheory.ElementaryEightDihedralExtension

/-!
# Recognizing the two elementary extensions inside a group of order32

Noncommutation makes the involution external to the central eight joined
with the cyclic four. That join is proper and has order strictly greater
than eight; Lagrange's theorem makes its index two. The external involution
therefore generates the whole original group with it, supplying the exact
inputs to the literal dihedral-extension theorem.
-/

public section
namespace Subgroup
variable {K : Type*} [Group K] [Finite K]

/-- In a group of order32, a central elementary eight and actual inverted
generators determine the two literal elementary-sixteen extensions without
any additional generation or externality hypotheses. -/
theorem elementaryEight_centralizer_extensions (hK : Nat.card K = 32)
    (E : Subgroup K) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEZ : E ≤ center K) (c b : K) (hc : orderOf c = 4) (hcE : c ^ 2 ∈ E)
    (hb : b ^ 2 = 1) (hbcne : ¬ Commute b c) (hbc : b * c * b⁻¹ = c⁻¹) :
    let A := E ⊔ zpowers b
    let B := E ⊔ zpowers (c * b)
    Nat.card K = 32 ∧ center K = E ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E ∧
      (∀ F : Subgroup K,
        (E ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  let D := E ⊔ zpowers c
  have hDC : D ≤ centralizer ({c} : Set K) := by
    refine sup_le (hEZ.trans (center_le_centralizer _)) (zpowers_le.mpr ?_)
    exact mem_centralizer_singleton_iff.mpr rfl
  have hbD : b ∉ D := fun he => hbcne
    (mem_centralizer_singleton_iff.mp (hDC he))
  have hcD : c ∈ D := mem_sup_right (mem_zpowers c)
  have hcnot : c ∉ E := by
    intro he
    have hh := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) c he)
    rw [hc] at hh
    norm_num at hh
  have hED : E ≤ D := le_sup_left
  have hlarge : 8 < Nat.card D := by
    have hle := card_le_of_le hED
    have hne : Nat.card D ≠ 8 := by
      intro he
      have hEq : E = D := eq_of_le_of_card_ge hED (by rw [he, hE])
      exact hcnot (hEq ▸ hcD)
    rw [hE] at hle
    omega
  have hdiv : 8 ∣ Nat.card D := hE ▸ card_dvd_of_le hED
  obtain ⟨n, hn⟩ := hdiv
  have hcard : 16 ≤ Nat.card D := by omega
  have hproper : D ≠ ⊤ := fun he => hbD (he ▸ mem_top b)
  have hindex := one_lt_index_of_ne_top hproper
  have hprod := D.card_mul_index
  rw [hK] at hprod
  have hiD : D.index = 2 := by nlinarith
  have hgen : D ⊔ zpowers b = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ D
    · exact mem_sup_left hx
    · have hxb : x * b⁻¹ ∈ D := by
        rw [D.mul_mem_iff_of_index_two hiD, D.inv_mem_iff]
        exact iff_of_false hx hbD
      simpa using (D ⊔ zpowers b).mul_mem (mem_sup_left hxb)
        (mem_sup_right (mem_zpowers b))
  exact elementaryEight_dihedral_extension E hE hEZ c b hc hcE hb hbD hbc hgen

end Subgroup
