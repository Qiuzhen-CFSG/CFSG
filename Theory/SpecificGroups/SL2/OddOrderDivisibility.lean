module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Order divisibility in small projective linear dimensions

The finite-field order formula gives `2|PSL₂(q)| = q(q²-1)` for odd q,
and `q³` divides `|PSL₃(q)|`. The proofs cancel only factors coprime to
q, keeping natural-number subtraction explicit. These are the arithmetic
inputs used in Aschbacher--Smith, G.7.2, printed pp.347--348.
-/

public section

namespace Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

/-- The odd-field PSL2 order formula without division. -/
theorem psl2_card_twice {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card PSL(2,F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hd : 2 ∣ Nat.card F - 1 := by
    obtain ⟨a, ha⟩ := hodd
    exact ⟨a, by omega⟩
  have hg : Nat.gcd 2 (Nat.card F - 1) = 2 := Nat.gcd_eq_left_iff_dvd.mpr hd
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [hg] at h
  norm_num [Fin.prod_univ_succ] at h
  have hfac : Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hfac] at h
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  calc
    Nat.card PSL(2,F) * 2 * (Nat.card F - 1) =
        (Nat.card F ^ 2 - 1) * (Nat.card F * (Nat.card F - 1)) := h
    _ = Nat.card F * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by ring

/-- The cube of the coefficient-field order divides the actual PSL3 order. -/
theorem psl3_cube_dvd_card {F : Type*} [Field F] [Finite F] :
    Nat.card F ^ 3 ∣ Nat.card PSL(3,F) := by
  let q := Nat.card F
  have hq : 1 ≤ q := Nat.le_of_lt (Finite.one_lt_card (α := F))
  have hcop : q.Coprime (q - 1) :=
    (Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [Fin.prod_univ_succ] at hc
  have h₁ : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  have h₂ : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  have hprod : q ^ 3 ∣ Nat.card PSL(3,F) * (Nat.gcd 3 (q - 1) * (q - 1)) := by
    rw [← mul_assoc, hc]
    change q ^ 3 ∣ (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2))
    rw [h₁, h₂]
    use (q ^ 3 - 1) * (q ^ 2 - 1) * (q - 1)
    ring
  exact ((hcop.of_dvd_right (Nat.gcd_dvd_right 3 (q - 1))).mul_right hcop).pow_left 3
    |>.dvd_of_dvd_mul_right hprod

/-- The prime thirteen divides PSL₃ over a three-element field. -/
theorem thirteen_dvd_card_psl3 {F : Type*} [Field F] [Finite F]
    (hcard : Nat.card F = 3) : 13 ∣ Nat.card PSL(3,F) := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hcard] at hc
  norm_num [Fin.prod_univ_succ] at hc
  have horder : Nat.card PSL(3,F) = 5616 := by omega
  rw [horder]
  norm_num

end Matrix.ProjectiveSpecialLinearGroup
