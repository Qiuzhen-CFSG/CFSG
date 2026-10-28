module

public import Theory.SpecificGroups.ReeF4.Field
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Binary rank-one normal forms

Two involutions satisfying the length-three braid relation define a map from
D₆. Distinct generators make this map faithful. The binary upper and lower
transvections satisfy these relations and generate the actual SL₂, giving the
marked rank-one comparison used by the F₄ end-node Levi.

This is the elementary A₁(2) presentation underlying Aschbacher–Smith
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
namespace ReeF4.Parabolics.BinaryLinear.LeviProductProof
open DihedralGroup
variable {G : Type*} [Group G]

@[expose] def word (a b : G) : DihedralGroup 3 → G
  | .r i => if i.val = 0 then 1 else if i.val = 1 then a * b else b * a
  | .sr i => if i.val = 0 then a else if i.val = 1 then b else a * b * a

set_option maxHeartbeats 800000 in
private lemma word_mul (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) (x y : DihedralGroup 3) :
    word a b (x * y) = word a b x * word a b y := by
  have haa (z : G) : a * (a * z) = z := by rw [← mul_assoc, ha, one_mul]
  have hbb (z : G) : b * (b * z) = z := by rw [← mul_assoc, hb, one_mul]
  have hbab : b * (a * b) = a * (b * a) := by simpa only [mul_assoc] using hab.symm
  have hbabc (z : G) : b * (a * (b * z)) = a * (b * (a * z)) := by
    simpa only [mul_assoc] using congrArg (· * z) hab.symm
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;>
    fin_cases x <;> fin_cases y <;> dsimp [word, ZMod.val] <;>
    simp +decide only [ite_true, ite_false, mul_assoc, ha, hb, haa, hbb, hbab, hbabc, one_mul, mul_one]

@[expose] def wordHom (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) : DihedralGroup 3 →* G where
  toFun := word a b
  map_one' := rfl
  map_mul' := by exact word_mul a b ha hb hab

lemma wordHom_injective (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) (hne : a ≠ b) :
    Function.Injective (wordHom a b ha hb hab) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hna : a ≠ 1 := by
    intro h
    have : b = 1 := by simpa [h, hb] using hab
    exact hne (h.trans this.symm)
  have hnb : b ≠ 1 := by
    intro h
    have : a = 1 := by simpa [h, ha] using hab.symm
    exact hne (this.trans h.symm)
  apply (injective_iff_map_eq_one (wordHom a b ha hb hab)).mpr
  intro x hx
  change word a b x = 1 at hx
  rcases x with i | i <;> fin_cases i <;> dsimp [word, ZMod.val] at hx <;> try rfl
  · exact hne ((eq_inv_iff_mul_eq_one.mpr hx).trans hbi) |>.elim
  · exact hne (((eq_inv_iff_mul_eq_one.mpr hx).trans hai).symm) |>.elim
  · exact (hna hx).elim
  · exact (hnb hx).elim
  · have : b = 1 := by
      have h := congrArg (fun z => a * z * a) hx
      simpa only [mul_assoc, ← mul_assoc a a, ha, one_mul, mul_one] using h
    exact (hnb this).elim

lemma wordHom_mem (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * a = b * a * b) (H : Subgroup G) (hA : a ∈ H) (hB : b ∈ H)
    (x : DihedralGroup 3) : wordHom a b ha hb hab x ∈ H := by
  rcases x with i | i <;> fin_cases i <;> dsimp [wordHom, word] <;>
    first | exact H.one_mem | exact hA | exact hB | exact H.mul_mem hA hB |
      exact H.mul_mem hB hA | exact H.mul_mem (H.mul_mem hA hB) hA


@[simp] lemma wordHom_sr0 (a b : G) (ha hb hab) :
    wordHom a b ha hb hab (.sr 0) = a := rfl
@[simp] lemma wordHom_sr1 (a b : G) (ha hb hab) :
    wordHom a b ha hb hab (.sr 1) = b := rfl

lemma map_word {H : Type*} [Group H] (f : G →* H) (a b : G) (x : DihedralGroup 3) :
    f (word a b x) = word (f a) (f b) x := by
  rcases x with i | i <;> fin_cases i <;> dsimp [word, ZMod.val] <;> simp only [map_one, map_mul]

lemma binary_scalar (t : CoefficientField 0) : t = 0 ∨ t = 1 := by
  have h : t * (t - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two]
    exact sub_eq_zero.mpr (by simpa using field_pow 0 t)
  exact (mul_eq_zero.mp h).imp_right sub_eq_zero.mp

open Matrix
noncomputable section
abbrev SL := SpecialLinearGroup (Fin 2) (CoefficientField 0)
@[expose] def slUpper : SL := SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) 1
@[expose] def slLower : SL := SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) 1

private lemma slUpper_sq : slUpper * slUpper = 1 := by
  rw [slUpper, ← SpecialLinearGroup.transvection_add]
  simp only [CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero]
private lemma slLower_sq : slLower * slLower = 1 := by
  rw [slLower, ← SpecialLinearGroup.transvection_add]
  simp only [CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero]
private lemma sl_braid : slUpper * slLower * slUpper = slLower * slUpper * slLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slUpper, slLower,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, CharTwo.add_self_eq_zero]
private lemma sl_ne : slUpper ≠ slLower := by
  intro h
  have he := congrArg (fun A : SL => A.val 0 1) h
  simp [slUpper, slLower, SpecialLinearGroup.transvection_coe] at he

private def slHom : DihedralGroup 3 →* SL := wordHom slUpper slLower slUpper_sq slLower_sq sl_braid

private lemma slHom_surjective : Function.Surjective slHom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  intro A _
  apply Matrix.SL2.transvection_induction (fun x => x ∈ slHom.range) ?_ ?_ A
  · intro i j hij t
    rcases binary_scalar t with rfl | rfl
    · simpa only [SpecialLinearGroup.transvection_coeff_zero] using slHom.range.one_mem
    · fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact ⟨.sr 0, rfl⟩
      · exact ⟨.sr 1, rfl⟩
      · exact (hij rfl).elim
  · exact fun A B hA hB => slHom.range.mul_mem hA hB

def slEquiv : DihedralGroup 3 ≃* SL := MulEquiv.ofBijective slHom
  ⟨wordHom_injective _ _ _ _ _ sl_ne, slHom_surjective⟩

@[simp] lemma slEquiv_sr0 : slEquiv (.sr 0) = slUpper := by
  exact wordHom_sr0 slUpper slLower slUpper_sq slLower_sq sl_braid
@[simp] lemma slEquiv_sr1 : slEquiv (.sr 1) = slLower := by
  exact wordHom_sr1 slUpper slLower slUpper_sq slLower_sq sl_braid
end
end ReeF4.Parabolics.BinaryLinear.LeviProductProof
