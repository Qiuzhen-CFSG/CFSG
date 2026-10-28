module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Rectangles
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangles
import Mathlib.Tactic.FinCases

/-!
# Marked intersection coordinates and their relative normalizers

The row meets the two rectangular root groups in its last three and two
coordinates, and the rectangles meet in the upper-right two-by-two block.
These explicit bijections give the source orders 8, 4, and 16.

An element of the transvection centralizer preserving a row intersection
has a zero lower-left block: apply it to the corresponding first-row roots.
The same holds for its inverse, so conjugation preserves the full rectangle.
The ambient fusion argument applying this calculation is in the parent module.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(3), 39.6(4), and the
marked parabolic intersections in 41.1, printed pp.213–215 and 219–220.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
private abbrev B := ZMod 2
private abbrev Mat := Matrix (Fin 5) (Fin 5) B

private theorem mem_rectangle_iff (k : ℕ) (hk : k = 2 ∨ k = 3) (g : SL) :
    g ∈ rectangle k ↔ ∀ i j : Fin 5, ¬ (i.val < k ∧ k ≤ j.val) →
      g i j = if i = j then 1 else 0 := by
  rcases hk with rfl | rfl
  · exact RectangleCoordinates.mem2_iff g
  · exact RectangleCoordinates.mem3_iff g

private theorem point_firstColumn (g : SL) (hg : g ∈ centralizer) :
    ∀ i : Fin 5, g i 0 = if i = 0 then 1 else 0 := by
  have hc := mem_centralizer_singleton_iff.mp hg
  have he (i : Fin 5) := congrArg (fun a : SL => a i 4) hc
  have hz (i : Fin 5) (hi : i ≠ 0) : g i 0 = 0 := by
    have h := he i
    change (g.val * (1 + Matrix.single 0 4 1) : Mat) i 4 =
      ((1 + Matrix.single 0 4 1) * g.val : Mat) i 4 at h
    simpa [Matrix.add_mul, Matrix.mul_add, hi, Matrix.single_mul_apply_of_ne] using h
  have h00 : g 0 0 = 1 := by
    apply (by decide : ∀ b : B, b ≠ 0 → b = 1)
    intro h
    apply g.det_ne_zero
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using h
    · exact hz i hi
  intro i
  by_cases hi : i = 0
  · simpa only [hi, ite_true] using h00
  · simpa only [if_neg hi] using hz i hi

private theorem conjugate_root_entry (g : SL) {i j : Fin 5} (hij : i < j)
    (a b : Fin 5) :
    (g * root hij * g⁻¹) a b = (if a = b then 1 else 0) + g a i * g⁻¹ j b := by
  have hinv : (g.val * (g⁻¹).val : Mat) = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun q : SL => (q : Mat)) (mul_inv_cancel g)
  change ((g.val * (1 + Matrix.single i j 1)) * (g⁻¹).val : Mat) a b = _
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply]
  apply congrArg ((if a = b then 1 else 0) + ·)
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, zero_mul]
  · simp

private theorem intersection_normalizer_lowerLeft (k : ℕ) (hk : k = 2 ∨ k = 3)
    (g : SL) (hg : g ∈ centralizer)
    (hn : g ∈ normalizer ((Model.row ⊓ rectangle k : Subgroup SL) : Set SL))
    (i j : Fin 5) (hi : k ≤ i.val) (hj : j.val < k) : g⁻¹ i j = 0 := by
  have h0i : (0 : Fin 5) < i := by rcases hk with rfl | rfl <;> omega
  have hr : root h0i ∈ Model.row ⊓ rectangle k :=
    ⟨subset_closure ⟨i, h0i, rfl⟩,
      subset_closure ⟨0, i, h0i, by rcases hk with rfl | rfl <;> decide, hi, rfl⟩⟩
  have hc := (mem_normalizer_iff.mp hn (root h0i)).mp hr
  have he := (mem_rectangle_iff k hk _).mp hc.2 0 j (by omega)
  rw [conjugate_root_entry, point_firstColumn g hg 0, if_pos rfl, one_mul] at he
  exact add_left_cancel (he.trans (add_zero _).symm)

/-- Inside the marked point centralizer, stabilizing the row intersection
forces stabilization of the full rectangular root group. -/
theorem model_normalizer_row_intersection (k : ℕ) (hk : k = 2 ∨ k = 3) :
    centralizer ⊓ normalizer ((Model.row ⊓ rectangle k : Subgroup SL) : Set SL) ≤
      normalizer (rectangle k : Set SL) := by
  rintro g ⟨hg, hn⟩
  have hlow := intersection_normalizer_lowerLeft k hk g hg hn
  have hlow' := intersection_normalizer_lowerLeft k hk g⁻¹
    (centralizer.inv_mem hg) ((normalizer _).inv_mem hn)
  simp only [inv_inv] at hlow'
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, hi, hj, rfl⟩
    change g * root hij * g⁻¹ ∈ rectangle k
    apply (mem_rectangle_iff k hk _).mpr
    intro a b hab
    rw [conjugate_root_entry]
    by_cases ha : a.val < k
    · have hb : b.val < k := by omega
      rw [hlow j b hj hb, mul_zero, add_zero]
    · rw [hlow' a i (by omega) hi, zero_mul, add_zero]
  · change Nat.card (rectangle k) ≤ Nat.card ((rectangle k).map (MulAut.conj g).toMonoidHom)
    have he := Nat.card_congr (Subgroup.equivMapOfInjective (rectangle k) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
    exact he.le

private theorem row_mem_plane_iff (a : Model.row) :
    (a : SL) ∈ Model.plane ↔ (modelRowCoordinates a).toAdd 0 = 0 := by
  constructor
  · intro ha
    have h := (RectangleCoordinates.mem2_iff a).mp ha 0 1 (by decide)
    rw [modelRowCoordinates_matrix] at h
    simpa [Matrix.single] using h
  · intro ha
    apply (RectangleCoordinates.mem2_iff a).mpr
    rw [modelRowCoordinates_matrix]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]

private theorem row_mem_threeSpace_iff (a : Model.row) :
    (a : SL) ∈ Model.threeSpace ↔
      (modelRowCoordinates a).toAdd 0 = 0 ∧ (modelRowCoordinates a).toAdd 1 = 0 := by
  constructor
  · intro ha
    constructor
    · have h := (RectangleCoordinates.mem3_iff a).mp ha 0 1 (by decide)
      rw [modelRowCoordinates_matrix] at h
      simpa [Matrix.single] using h
    · have h := (RectangleCoordinates.mem3_iff a).mp ha 0 2 (by decide)
      rw [modelRowCoordinates_matrix] at h
      simpa [Matrix.single] using h
  · rintro ⟨h0, h1⟩
    apply (RectangleCoordinates.mem3_iff a).mpr
    rw [modelRowCoordinates_matrix]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]

/-- The row-plane intersection has exactly its three terminal row coordinates. -/
def modelRowPlaneCoordinates : ↥(Model.row ⊓ Model.plane) ≃ (Fin 3 → ZMod 2) where
  toFun a i := (modelRowCoordinates ⟨a, a.property.1⟩).toAdd i.succ
  invFun v :=
    ⟨modelRowCoordinates.symm (Multiplicative.ofAdd (Fin.cons 0 v)),
      (modelRowCoordinates.symm _).property, by
        apply (row_mem_plane_iff _).mpr
        simp⟩
  left_inv a := by
    apply Subtype.ext
    have h : modelRowCoordinates.symm
        (Multiplicative.ofAdd (Fin.cons 0 (fun i =>
          (modelRowCoordinates ⟨a, a.property.1⟩).toAdd i.succ))) =
        (⟨a, a.property.1⟩ : Model.row) := by
      apply modelRowCoordinates.injective
      simp only [modelRowCoordinates.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ((row_mem_plane_iff _).mp a.property.2).symm
      · rfl
    exact congrArg (fun x : Model.row => (x : SL)) h
  right_inv v := by funext i; simp

/-- The row-three-space intersection has its two terminal row coordinates. -/
def modelRowThreeSpaceCoordinates : ↥(Model.row ⊓ Model.threeSpace) ≃ (Fin 2 → ZMod 2) where
  toFun a i := (modelRowCoordinates ⟨a, a.property.1⟩).toAdd i.succ.succ
  invFun v :=
    ⟨modelRowCoordinates.symm (Multiplicative.ofAdd (Fin.cons 0 (Fin.cons 0 v))),
      (modelRowCoordinates.symm _).property, by
        apply (row_mem_threeSpace_iff _).mpr
        simp⟩
  left_inv a := by
    apply Subtype.ext
    have h : modelRowCoordinates.symm
        (Multiplicative.ofAdd (Fin.cons 0 (Fin.cons 0 (fun i =>
          (modelRowCoordinates ⟨a, a.property.1⟩).toAdd i.succ.succ)))) =
        (⟨a, a.property.1⟩ : Model.row) := by
      apply modelRowCoordinates.injective
      simp only [modelRowCoordinates.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · exact ((row_mem_threeSpace_iff _).mp a.property.2).1.symm
      · exact ((row_mem_threeSpace_iff _).mp a.property.2).2.symm
      · rfl
    exact congrArg (fun x : Model.row => (x : SL)) h
  right_inv v := by funext i; simp

private theorem plane_mem_threeSpace_iff (a : Model.plane) :
    (a : SL) ∈ Model.threeSpace ↔ ∀ i : Fin 2, (modelPlaneCoordinates a).toAdd i 0 = 0 := by
  constructor
  · intro ha i
    rw [modelPlaneCoordinates_apply]
    fin_cases i
    · simpa using (RectangleCoordinates.mem3_iff a).mp ha 0 2 (by decide)
    · simpa using (RectangleCoordinates.mem3_iff a).mp ha 1 2 (by decide)
  · intro ha
    apply (RectangleCoordinates.mem3_iff a).mpr
    rw [modelPlaneCoordinates_matrix]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]

/-- The intersection of the two rectangles is the literal upper-right
two-by-two block, with four independent binary coordinates. -/
def modelPlanesIntersectionCoordinates :
    ↥(Model.plane ⊓ Model.threeSpace) ≃ (Fin 2 → Fin 2 → ZMod 2) where
  toFun a i j := (modelPlaneCoordinates ⟨a, a.property.1⟩).toAdd i j.succ
  invFun v :=
    ⟨modelPlaneCoordinates.symm (Multiplicative.ofAdd (fun i => Fin.cons 0 (v i))),
      (modelPlaneCoordinates.symm _).property, by
        apply (plane_mem_threeSpace_iff _).mpr
        intro i
        simp⟩
  left_inv a := by
    apply Subtype.ext
    have h : modelPlaneCoordinates.symm
        (Multiplicative.ofAdd (fun i => Fin.cons 0 (fun j =>
          (modelPlaneCoordinates ⟨a, a.property.1⟩).toAdd i j.succ))) =
        (⟨a, a.property.1⟩ : Model.plane) := by
      apply modelPlaneCoordinates.injective
      simp only [modelPlaneCoordinates.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext i j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact ((plane_mem_threeSpace_iff _).mp a.property.2 i).symm
      · rfl
    exact congrArg (fun x : Model.plane => (x : SL)) h
  right_inv v := by funext i j; simp

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
