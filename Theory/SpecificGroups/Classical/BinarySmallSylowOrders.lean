module

public import Theory.SpecificGroups.Classical.SmallSylowOrders
/-!
# Binary degree-three two-parts

The fraction-free PSL₃ order and the actual projective-unitary order show
that the full unipotent two-part survives the odd scalar quotient. These
bounds apply directly to the field and Hermitian form in the source model.
They supply the numeric exclusions in Aschbacher–Smith F.6.18, p.310.
-/

public section
open scoped MatrixGroups
namespace Theory.ClassicalSmallSylow
private theorem even_psl3_card_gcd {F : Type*} [Field F] [Finite F] :
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

theorem binary_psl3_two_power_dvd {F : Type*} [Field F] [Finite F]
    {f r : ℕ} (hc : Nat.card F = 2 ^ f) (hr : r ≤ 3 * f) :
    2 ^ r ∣ Nat.card PSL(3,F) := by
  have hd : 2 ^ r ∣ Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) := by
    rw [even_psl3_card_gcd,hc]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  exact ((show Nat.Coprime (2 ^ r) 3 from (by decide : Nat.Coprime 2 3).pow_left r).of_dvd_right
    (Nat.gcd_dvd_left _ _)).dvd_of_dvd_mul_right hd

theorem binary_psu3_two_power_dvd {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {f r : ℕ} (hf : 1 ≤ f)
    (hc : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hr : r ≤ 3 * f) :
    2 ^ r ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let q := 2 ^ f
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  rw [BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective J hc hconj]
  have htwo : 2 ^ r ∣ q ^ 3 := by
    change 2 ^ r ∣ (2 ^ f) ^ 3
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have hd : 2 ^ r ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right htwo _) _
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply (Nat.gcd_dvd_right 3 (q + 1)).trans
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact ⟨q ^ 2 - q + 1, by nlinarith [Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)]⟩
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  exact ((show Nat.Coprime (2 ^ r) (Nat.gcd 3 (q + 1)) from
    ((by decide : Nat.Coprime 2 3).pow_left r).of_dvd_right
      (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd hg)
end Theory.ClassicalSmallSylow
