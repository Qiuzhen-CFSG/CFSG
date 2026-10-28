module
public import ABG.ChapterII.Section1.WreathedNormalForm
public import ABG.ChapterII.Section1.WreathedBase
public import ABG.ChapterII.Section1.WreathedRelations

/-!
# Outer conjugation on the wreathed base involutions

For the chosen presentation in ABG Chapter II §1 (article p.9), every element
outside the abelian base exchanges the two coordinate involutions x₂ and x₃.
Write the element as b*z with b in the base. Conjugation by z exchanges the
generators and their half-powers, while b centralizes both half-powers. These
formulas support Lemma 2's involution classes and invariant-subgroup clause.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem outer_form {g : S} (hg : g ∉ P.U) :
    ∃ b ∈ P.U, g = b * P.z := by
  obtain ⟨i,j,k,h⟩ := P.exists_normal_form g
  have hb : P.s ^ i.val * P.t ^ j.val ∈ P.U :=
    (P.mem_U_iff _).mpr ⟨i.val, j.val, by simp⟩
  have hk : k.val = 1 := by
    have hk' := k.isLt
    by_contra hne
    have hz : k.val = 0 := by omega
    apply hg
    simpa [← h, hz] using hb
  exact ⟨_, hb, by simpa [hk] using h.symm⟩

public theorem outer_conj_x₂ {g : S} (hg : g ∉ P.U) :
    g * P.x₂ * g⁻¹ = P.x₃ := by
  obtain ⟨b, hb, rfl⟩ := P.outer_form hg
  have hx₃ : P.x₃ ∈ P.U := (P.mem_U_iff _).mpr
    ⟨0, ((2 ^ (n-1) : ℕ) : ℤ), by simp only [zpow_zero, one_mul, zpow_natCast, x₃]⟩
  have hz : P.z * P.x₂ * P.z⁻¹ = P.x₃ := by
    rw [x₂, P.z_mul_s_pow, mul_inv_cancel_right]
    rfl
  calc
    _ = b * (P.z * P.x₂ * P.z⁻¹) * b⁻¹ := by group
    _ = b * P.x₃ * b⁻¹ := by rw [hz]
    _ = P.x₃ := by rw [(P.commute_of_mem_U hb hx₃).eq]; group

public theorem outer_conj_x₃ {g : S} (hg : g ∉ P.U) :
    g * P.x₃ * g⁻¹ = P.x₂ := by
  obtain ⟨b, hb, rfl⟩ := P.outer_form hg
  have hx₂ : P.x₂ ∈ P.U := (P.mem_U_iff _).mpr
    ⟨((2 ^ (n-1) : ℕ) : ℤ), 0, by simp only [zpow_zero, mul_one, zpow_natCast, x₂]⟩
  have hz : P.z * P.x₃ * P.z⁻¹ = P.x₂ := by
    rw [x₃, P.z_mul_t_pow, mul_inv_cancel_right]
    rfl
  calc
    _ = b * (P.z * P.x₃ * P.z⁻¹) * b⁻¹ := by group
    _ = b * P.x₂ * b⁻¹ := by rw [hz]
    _ = P.x₂ := by rw [(P.commute_of_mem_U hb hx₂).eq]; group
end ABG.Wreathed.Presentation
