module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Shape
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Census
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The literal non-root involution orbit in the point two-core

The square-one condition in the seven-coordinate core shape is the zero
pairing of the row and column vectors. Outside the two root groups both
vectors are nonzero. The checked normal-form words are realized by seven
actual elementary matrices centralizing the marked transvection. Their
conjugation formulas take every such involution to I+E₀₂+E₁₄, the rank-two
rectangle element used to exclude fusion with the distinguished involution.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(5), 39.4, pp.213–214.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
open UniquenessLinear
private abbrev B := ZMod 2
private abbrev Mat := Matrix (Fin 5) (Fin 5) B

@[expose] def entries (v : Coords) : Matrix (Fin 5) (Fin 5) (ZMod 2) := !![
  1,v 0,v 1,v 2,v 3;
  0,1,0,0,v 4;
  0,0,1,0,v 5;
  0,0,0,1,v 6;
  0,0,0,0,1]
@[expose] def coordinates (g : SL) : Coords := ![g 0 1,g 0 2,g 0 3,g 0 4,g 1 4,g 2 4,g 3 4]

private def generator : Fin 7 → SL :=
  ![Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 2) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 1) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 3) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 2) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 2) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 3) 1]
private theorem generator_inv (k : Fin 7) : (generator k)⁻¹ = generator k := by
  fin_cases k <;> simp [generator, Matrix.SpecialLinearGroup.transvection_inv,
    show (-1 : B) = 1 from rfl]
private theorem generator_mem (k : Fin 7) : generator k ∈ centralizer := by
  have h : ∀ k : Fin 7, generator k ∈ centralizer := by
    intro j
    apply mem_centralizer_singleton_iff.mpr
    have cert : ∀ j : Fin 7, generator j * transvection = transvection * generator j := by decide +kernel
    exact cert j
  exact h k

private theorem generator_action_0 (v : Coords) :
    (generator 0).val * entries v * (generator 0).val = entries (step 0 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl]

private theorem generator_action_1 (v : Coords) :
    (generator 1).val * entries v * (generator 1).val = entries (step 1 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl]

private theorem generator_action_2 (v : Coords) :
    (generator 2).val * entries v * (generator 2).val = entries (step 2 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl]

private theorem generator_action_3 (v : Coords) :
    (generator 3).val * entries v * (generator 3).val = entries (step 3 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl]

private theorem generator_action_4 (v : Coords) :
    (generator 4).val * entries v * (generator 4).val = entries (step 4 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl, zero_add]

private theorem generator_action_5 (v : Coords) :
    (generator 5).val * entries v * (generator 5).val = entries (step 5 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl, zero_add]

private theorem generator_action_6 (v : Coords) :
    (generator 6).val * entries v * (generator 6).val = entries (step 6 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, entries, step, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single, Matrix.add_apply]
  all_goals ring_nf
  all_goals simp only [show (2 : B) = 0 from rfl, zero_add]

private theorem generator_action (k : Fin 7) (v : Coords) :
    (generator k).val * entries v * (generator k).val = entries (step k v) := by
  fin_cases k
  · exact generator_action_0 v
  · exact generator_action_1 v
  · exact generator_action_2 v
  · exact generator_action_3 v
  · exact generator_action_4 v
  · exact generator_action_5 v
  · exact generator_action_6 v

private theorem exists_word_conjugator (w : List (Fin 7)) (q : SL) (v : Coords)
    (hq : q.val = entries v) :
    ∃ c : centralizer, ((c : SL) * q * (c : SL)⁻¹).val =
      entries (w.foldl (fun u k => step k u) v) := by
  induction w generalizing q v with
  | nil => exact ⟨1, by simpa using hq⟩
  | cons k w ih =>
    have hk : (generator k * q * (generator k)⁻¹).val = entries (step k v) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        generator_inv, hq, generator_action]
    obtain ⟨c,hc⟩ := ih _ _ hk
    refine ⟨c * ⟨generator k,generator_mem k⟩, ?_⟩
    change (((c : SL) * generator k) * q * ((c : SL) * generator k)⁻¹).val = _
    have he : ((c : SL) * generator k) * q * ((c : SL) * generator k)⁻¹ =
        (c : SL) * (generator k * q * (generator k)⁻¹) * (c : SL)⁻¹ := by group
    rw [he]
    exact hc

private def columnWord (a b c d : B) : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 4) a *
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 4) b *
  Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 4) c *
  Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 4) d
private theorem columnWord_val (a b c d : B) : (columnWord a b c d).val =
    1 + Matrix.single 0 4 a + Matrix.single 1 4 b + Matrix.single 2 4 c + Matrix.single 3 4 d := by
  simp [columnWord, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add,
    Matrix.add_mul, Matrix.single_mul_single_of_ne, add_assoc]
private theorem columnWord_mem (a b c d : B) : columnWord a b c d ∈ Model.column := by
  have hm (i : Fin 5) (hi : i < 4) (a : B) :
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hi) a ∈ Model.column := by
    rcases (by decide : ∀ a : B, a = 0 ∨ a = 1) a with rfl | rfl
    · simp
    · exact subset_closure ⟨i,hi,rfl⟩
  exact Model.column.mul_mem (Model.column.mul_mem (Model.column.mul_mem
    (hm 0 (by decide) a) (hm 1 (by decide) b)) (hm 2 (by decide) c)) (hm 3 (by decide) d)

private theorem row_mem (q : SL) (v : Coords) (hq : q.val = entries v)
    (hv : v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0) : q ∈ Model.row := by
  let u := modelRowCoordinates.symm (Multiplicative.ofAdd ![v 0,v 1,v 2,v 3])
  have he : q = u.val := by
    apply Subtype.ext
    rw [hq,modelRowCoordinates_matrix,modelRowCoordinates.apply_symm_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries,Matrix.single,hv.1,hv.2.1,hv.2.2]
  exact he ▸ u.property

private theorem column_mem (q : SL) (v : Coords) (hq : q.val = entries v)
    (hv : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) : q ∈ Model.column := by
  have he : q = columnWord (v 3) (v 4) (v 5) (v 6) := by
    apply Subtype.ext
    rw [hq,columnWord_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries,Matrix.single,hv.1,hv.2.1,hv.2.2]
  rw [he]
  exact columnWord_mem _ _ _ _

/-- Every involution in the actual two-core outside the two marked root
groups is carried to the same rank-two rectangle element by an element of
the actual transvection centralizer. -/
theorem core_involution_conjugator (q : centralizer) (hq : q ∈ pCore 2 centralizer)
    (hs : (q : SL) ^ 2 = 1) (hr : (q : SL) ∉ Model.row) (hc : (q : SL) ∉ Model.column) :
    ∃ c : centralizer, ((c : SL) * (q : SL) * (c : SL)⁻¹).val = entries representative := by
  let v := coordinates q
  have hqv : q.val.val = entries v := core_shape q hq
  have hsq : v 0 * v 4 + v 1 * v 5 + v 2 * v 6 = 0 := by
    have he := congrArg (fun g : SL => g 0 4) hs
    rw [pow_two] at he
    change (q.val.val * q.val.val) 0 4 = (1 : Mat) 0 4 at he
    rw [hqv] at he
    have hd : ∀ a : B, a + a = 0 := by decide
    have he' : v 3 + v 0 * v 4 + v 1 * v 5 + v 2 * v 6 + v 3 = 0 := by
      simpa [entries, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, ← add_assoc] using he
    calc
      _ = (v 3 + v 3) + (v 0 * v 4 + v 1 * v 5 + v 2 * v 6) := by rw [hd,zero_add]
      _ = v 3 + v 0 * v 4 + v 1 * v 5 + v 2 * v 6 + v 3 := by ac_rfl
      _ = 0 := he'
  have hr' : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := fun h => hc (column_mem q v hqv h)
  have hc' : ¬ (v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0) := fun h => hr (row_mem q v hqv h)
  obtain ⟨c,hc⟩ := exists_word_conjugator (path v) q v hqv
  rw [core_normal_form v hsq hr' hc'] at hc
  exact ⟨c,hc⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
