module

public import Theory.SpecificGroups.Classical.SmallSylowOrders

/-!
# Prime-field congruences for the small degree-three Sylow branches

For PSL₃(q), q congruent to one modulo eight forces 128 to divide the
order. For PSU₃(q), the analogous forbidden residue is seven. The scalar
kernel has odd order, so it cannot remove this factor. A Sylow subgroup
of order at most 64 therefore strengthens the linear sign q≡1 modulo
four to q≡5 modulo eight, and the unitary sign q≡3 to q≡3 modulo eight.

Source: the classical order formulas and Aschbacher--Smith F.6.18(10)--(11),
printed pp.309--310.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.ClassicalSmallSylow

private theorem not_128_dvd_of_sylow_le_64 {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (hP : Nat.card P ≤ 64) : ¬ 128 ∣ Nat.card G := by
  intro hd
  have h := P.pow_dvd_card_of_pow_dvd_card (n := 7) hd
  have := Nat.le_of_dvd (Nat.card_pos (α := P)) h
  norm_num at this
  omega

private theorem square_sub_dvd_sixteen {q : ℕ} (hq : 1 < q)
    (hm : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q ^ 2 - 1 := by
  apply Nat.dvd_of_mod_eq_zero
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have hsub : (q ^ 2 - 1) % 16 = (q ^ 2 + 15) % 16 := by omega
  have hb := Nat.mod_lt q (by decide : 0 < 16)
  have hr : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
  rcases hr with he | he | he | he <;>
    simp [hsub, Nat.add_mod, Nat.pow_mod, he]

private theorem psl3_card_identity {F : Type*} [Field F] [Finite F] :
    Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [Fin.prod_univ_succ] at h
  have h₁ : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  have h₂ : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    ring_nf
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  calc
    _ = (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := h
    _ = _ := by rw [h₁, h₂]; ring

/-- The linear residue one modulo eight forces too large a two-part. -/
theorem psl3_128_dvd_of_mod_eight_one {F : Type*} [Field F] [Finite F]
    (hm : Nat.card F % 8 = 1) : 128 ∣ Nat.card PSL(3,F) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h8 : 8 ∣ q ^ 3 - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    have hc : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hsub : (q ^ 3 - 1) % 8 = (q ^ 3 + 7) % 8 := by omega
    simp [hsub, Nat.add_mod, Nat.pow_mod, show q % 8 = 1 from hm]
  have h16 := square_sub_dvd_sixteen hq (Or.inl hm)
  have hd : 128 ∣ Nat.card PSL(3,F) * Nat.gcd 3 (q - 1) := by
    rw [psl3_card_identity]
    simpa only [mul_assoc] using dvd_mul_of_dvd_right (Nat.mul_dvd_mul h8 h16) (q ^ 3)
  exact (show Nat.Coprime 128 (Nat.gcd 3 (q - 1)) from
    (by decide : Nat.Coprime 128 3).of_dvd_right (Nat.gcd_dvd_left _ _)).dvd_of_dvd_mul_right hd

/-- The unitary residue seven modulo eight forces too large a two-part. -/
theorem psu3_128_dvd_of_mod_eight_seven {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {q : ℕ} (hq : 1 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q)
    (hm : q % 8 = 7) : 128 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have h8 : 8 ∣ q ^ 3 + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hm]
  have h16 := square_sub_dvd_sixteen hq (Or.inr hm)
  rw [HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective J hc hj]
  have hd : 128 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    rw [mul_right_comm]
    exact dvd_mul_of_dvd_left (Nat.mul_dvd_mul h8 h16) _
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply (Nat.gcd_dvd_right 3 (q + 1)).trans
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact ⟨q ^ 2 - q + 1, by nlinarith [Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)]⟩
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  exact ((show Nat.Coprime 128 (Nat.gcd 3 (q + 1)) from
    (by decide : Nat.Coprime 128 3).of_dvd_right (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd hg)

/-- The sign and actual Sylow bound give the exact linear congruence. -/
theorem psl3_mod_eight_of_small_sylow {F : Type*} [Field F] [Finite F]
    (P : Sylow 2 PSL(3,F)) (hP : Nat.card P ≤ 64)
    (hs : Nat.card F % 4 = 1) : Nat.card F % 8 = 5 := by
  have hn := not_128_dvd_of_sylow_le_64 P hP
  have hm : Nat.card F % 8 ≠ 1 := fun h => hn (psl3_128_dvd_of_mod_eight_one h)
  omega

/-- The sign and actual Sylow bound give the exact unitary congruence. -/
theorem psu3_mod_eight_of_small_sylow {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {q : ℕ} (hq : 1 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (hP : Nat.card P ≤ 64)
    (hs : q % 4 = 3) : q % 8 = 3 := by
  have hn := not_128_dvd_of_sylow_le_64 P hP
  have hm : q % 8 ≠ 7 := fun h => hn (psu3_128_dvd_of_mod_eight_seven J hq hc hj h)
  omega

end Theory.ClassicalSmallSylow
