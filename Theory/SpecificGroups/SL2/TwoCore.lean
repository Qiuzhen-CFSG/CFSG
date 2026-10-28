module

public import Theory.PGroupCore
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FinCases

/-!
# The defining two-core of SL₂

A normal two-subgroup has a nonzero fixed vector on the natural module in
characteristic two. Normality then makes the first basis vector fixed, by
completing the fixed vector to a determinant-one matrix. Conjugating by the
coordinate swap makes the second basis vector fixed as well. Thus the subgroup
is trivial. This argument includes the field of order two.

This supplies the quotient-core step for Aschbacher--Smith F.1.12(I)(6),
printed pp. 263--264 of `refs/quasithin.pdf`.
-/

open Matrix
public noncomputable section
namespace Matrix.SL2
variable (F : Type*) [Field F] [CharP F 2]
private def swapMatrix : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0], by simp [det_fin_two, CharTwo.neg_eq]⟩

omit [CharP F 2] in
private theorem exists_first_column (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) F, g • (![1,0] : Fin 2 → F) = v := by
  by_cases h : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; ext i; fin_cases i <;> simp_all
    refine ⟨⟨!![v 0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    change (!![v 0, -(v 1)⁻¹; v 1, 0] *ᵥ ![1,0]) = v
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h]⟩, ?_⟩
    change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ ![1,0]) = v
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- This includes the binary field; no simplicity hypothesis is needed. -/
theorem twoCore_eq_bot [Finite F] : pCore 2 (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  let := Fintype.ofFinite F
  let N := pCore 2 (SpecialLinearGroup (Fin 2) F)
  have hcard : 2 ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    have h : 2 ∣ Fintype.card F :=
      (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
    exact dvd_pow h (by decide : 2 ≠ 0)
  have hz : (0 : Fin 2 → F) ∈ MulAction.fixedPoints N (Fin 2 → F) := by
    intro g
    change g.val.val *ᵥ 0 = 0
    exact mulVec_zero _
  have hN : IsPGroup 2 N := pCore_isPGroup
  obtain ⟨v,hv,hv0⟩ := hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 2 → F) hcard hz
  obtain ⟨g,hg⟩ := exists_first_column F v (Ne.symm hv0)
  have hfix (a : SpecialLinearGroup (Fin 2) F) (ha : a ∈ N)
      (b : SpecialLinearGroup (Fin 2) F) : a • (b • v) = b • v := by
    have hn := (inferInstance : N.Normal).conj_mem' a ha b
    have h := hv ⟨b⁻¹ * a * b, hn⟩
    change (b⁻¹ * a * b) • v = v at h
    have := congrArg (fun w => b • w) h
    simpa only [mul_smul, smul_inv_smul] using this
  have he0 (a : SpecialLinearGroup (Fin 2) F) (ha : a ∈ N) :
      a • (![1,0] : Fin 2 → F) = ![1,0] := by
    have h := hfix a ha g⁻¹
    rw [← hg, inv_smul_smul] at h
    exact h
  have he1 (a : SpecialLinearGroup (Fin 2) F) (ha : a ∈ N) :
      a • (![0,1] : Fin 2 → F) = ![0,1] := by
    have hn := (inferInstance : N.Normal).conj_mem' a ha (swapMatrix F)
    have h := he0 _ hn
    have hh := congrArg (fun w => swapMatrix F • w) h
    simp only [mul_smul, smul_inv_smul] at hh
    have hs : swapMatrix F • (![1,0] : Fin 2 → F) = ![0,1] := by
      change (!![0,1;1,0] *ᵥ ![1,0]) = ![0,1]
      ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
    rwa [hs] at hh
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have h0 := he0 a ha
  have h1 := he1 a ha
  change a.val *ᵥ ![1,0] = ![1,0] at h0
  change a.val *ᵥ ![0,1] = ![0,1] at h1
  apply Subtype.ext
  ext i j
  have h00 := congrFun h0 0
  have h10 := congrFun h0 1
  have h01 := congrFun h1 0
  have h11 := congrFun h1 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h00 h10 h01 h11
  fin_cases i <;> fin_cases j <;> simp_all

end Matrix.SL2
