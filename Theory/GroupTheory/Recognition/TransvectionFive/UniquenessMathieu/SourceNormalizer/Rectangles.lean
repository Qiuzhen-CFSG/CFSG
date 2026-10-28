module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceColumn
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFlag
import Mathlib.Tactic.FinCases

/-!
# Coordinates and self-centralization of the marked binary rectangle

A word in the six roots crossing the cut 2+3 has precisely its six displayed
entries. The off-diagonal blocks multiply to zero, so these coordinates give
an isomorphism with the additive binary six-space. Commutation with the same
roots forces a centralizing matrix to have scalar diagonal blocks; over the
binary field their diagonal entries must be one. The full centralizer is
therefore the rectangle itself.

These are model inputs to the ambient quotient actions in §§39–40 of
Aschbacher, *Sporadic Groups* (1994), printed pp.213–219. They do not identify
the ambient normalizer with the relative normalizer in the point centralizer.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear

private abbrev Six := Fin 2 → Fin 3 → ZMod 2
private abbrev trans {i j : Fin 5} (h : i < j) (a : ZMod 2) : SL :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt h) a
private def planeWord (v : Six) : SL :=
  trans (by decide : (0 : Fin 5) < 2) (v 0 0) *
  trans (by decide : (0 : Fin 5) < 3) (v 0 1) *
  trans (by decide : (0 : Fin 5) < 4) (v 0 2) *
  trans (by decide : (1 : Fin 5) < 2) (v 1 0) *
  trans (by decide : (1 : Fin 5) < 3) (v 1 1) *
  trans (by decide : (1 : Fin 5) < 4) (v 1 2)
private theorem planeWord_val (v : Six) :
    (planeWord v).val = 1 + Matrix.single 0 2 (v 0 0) +
      Matrix.single 0 3 (v 0 1) + Matrix.single 0 4 (v 0 2) +
      Matrix.single 1 2 (v 1 0) + Matrix.single 1 3 (v 1 1) +
      Matrix.single 1 4 (v 1 2) := by
  simp [planeWord, trans, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]
private theorem planeWord_entry (v : Six) (i : Fin 2) (j : Fin 3) :
    planeWord v (i.castLE (by decide)) (j.natAdd 2) = v i j := by
  rw [planeWord_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]
private theorem planeWord_mem (v : Six) : planeWord v ∈ Model.plane := by
  have h (i j : Fin 5) (hij : i < j) (hi : i.val < 2) (hj : 2 ≤ j.val) (a : ZMod 2) :
      trans hij a ∈ Model.plane := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simp
    · exact subset_closure ⟨i, j, hij, hi, hj, rfl⟩
  unfold planeWord
  repeat' apply Model.plane.mul_mem
  all_goals exact h _ _ _ (by decide) (by decide) _
private def planeBlock (v : Six) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if h : i.val < 2 ∧ 2 ≤ j.val then v ⟨i.val, h.1⟩ ⟨j.val - 2, by omega⟩ else 0
private theorem planeWord_block (v : Six) : (planeWord v).val = 1 + planeBlock v := by
  rw [planeWord_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeBlock, Matrix.single]
private theorem planeBlock_add (v w : Six) : planeBlock (v + w) = planeBlock v + planeBlock w := by
  ext i j
  simp only [planeBlock, Matrix.add_apply]
  split_ifs <;> rfl
private theorem planeBlock_mul (v w : Six) : planeBlock v * planeBlock w = 0 := by
  ext i j
  change ∑ k, planeBlock v i k * planeBlock w k j = 0
  apply Finset.sum_eq_zero
  intro k _
  simp only [planeBlock]
  split_ifs with h₁ h₂ <;> try simp
  omega
private def planeWordHom : Multiplicative Six →* SL where
  toFun v := planeWord v.toAdd
  map_one' := by apply Subtype.ext; simp [planeWord_val]
  map_mul' v w := by
    apply Subtype.ext
    change (planeWord (v.toAdd + w.toAdd)).val = (planeWord v.toAdd).val * (planeWord w.toAdd).val
    simp only [planeWord_block, planeBlock_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, planeBlock_mul, add_zero]
    exact (add_assoc _ _ _).symm
private theorem planeWordHom_range : planeWordHom.range = Model.plane := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact planeWord_mem v.toAdd
  · apply (closure_le _).mpr
    rintro _ ⟨i, j, hij, hi, hj, rfl⟩
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    refine ⟨Multiplicative.ofAdd (fun a b => if a.val = i.val ∧ b.val + 2 = j.val then 1 else 0), ?_⟩
    apply Subtype.ext
    change (planeWord _).val = (root hij).val
    rw [planeWord_val]
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
      simp [root, Matrix.SpecialLinearGroup.transvection_coe]

private def planeParam : Multiplicative Six →* Model.plane :=
  planeWordHom.codRestrict Model.plane (fun v => planeWord_mem v.toAdd)
private theorem planeParam_injective : Function.Injective planeParam := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i j
  have he := congrArg (fun a : Model.plane => (a : SL) (i.castLE (by decide)) (j.natAdd 2)) h
  change planeWord v.toAdd _ _ = planeWord w.toAdd _ _ at he
  simpa only [planeWord_entry] using he
private theorem planeParam_surjective : Function.Surjective planeParam := by
  intro a
  have ha : (a : SL) ∈ planeWordHom.range := by rw [planeWordHom_range]; exact a.property
  obtain ⟨v, hv⟩ := ha
  exact ⟨v, Subtype.ext hv⟩

/-- The six entries of the literal rectangular root group, with their group law. -/
def modelPlaneCoordinates : Model.plane ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  (MulEquiv.ofBijective planeParam ⟨planeParam_injective, planeParam_surjective⟩).symm

/-- Coordinates are the six entries in the marked two-by-three rectangle. -/
theorem modelPlaneCoordinates_apply (a : Model.plane) (i : Fin 2) (j : Fin 3) :
    (modelPlaneCoordinates a).toAdd i j = (a : SL) (i.castLE (by decide)) (j.natAdd 2) := by
  have he : planeParam (modelPlaneCoordinates a) = a :=
    (MulEquiv.ofBijective planeParam ⟨planeParam_injective, planeParam_surjective⟩).apply_symm_apply a
  have h := congrArg (fun a : Model.plane => (a : SL) (i.castLE (by decide)) (j.natAdd 2)) he
  exact (planeWord_entry _ i j).symm.trans h

/-- The six marked entries determine the whole matrix, including its
identity diagonal and all forced zero entries. -/
theorem modelPlaneCoordinates_matrix (a : Model.plane) :
    (a : SL).val = 1 + Matrix.single 0 2 ((modelPlaneCoordinates a).toAdd 0 0) +
      Matrix.single 0 3 ((modelPlaneCoordinates a).toAdd 0 1) +
      Matrix.single 0 4 ((modelPlaneCoordinates a).toAdd 0 2) +
      Matrix.single 1 2 ((modelPlaneCoordinates a).toAdd 1 0) +
      Matrix.single 1 3 ((modelPlaneCoordinates a).toAdd 1 1) +
      Matrix.single 1 4 ((modelPlaneCoordinates a).toAdd 1 2) := by
  have he : planeParam (modelPlaneCoordinates a) = a :=
    (MulEquiv.ofBijective planeParam ⟨planeParam_injective, planeParam_surjective⟩).apply_symm_apply a
  exact (congrArg (fun a : Model.plane => (a : SL).val) he).symm.trans (planeWord_val _)

private theorem centralizer_root_entry (g : SL) {i j : Fin 5} (hij : i < j)
    (hc : g * root hij = root hij * g) (k l : Fin 5) :
    (if k = i then g j l else 0) = (if l = j then g k i else 0) := by
  have he := congrArg (fun a : SL => a k l) hc.symm
  change (((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) + Matrix.single i j 1) * g.val : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l =
    (g.val * (1 + Matrix.single i j 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l at he
  by_cases hk : k = i <;> by_cases hl : l = j
  · subst k; subst l
    simpa [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_apply_same,
      Matrix.mul_single_apply_same] using he
  · subst k
    simpa [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_apply_same,
      Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, hl] using he
  · subst l
    have hh : g k i = 0 := by
      simpa [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk,
        Matrix.mul_single_apply_same, hk] using he
    simpa only [if_neg hk, ite_true] using hh.symm
  · simp [hk, hl]

private theorem centralizer_plane_pattern (g : SL)
    (hg : g ∈ Subgroup.centralizer (Model.plane : Set SL)) :
    (∀ i j : Fin 5, 2 ≤ i.val → g i j = if i = j then g 0 0 else 0) ∧
    g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = g 0 0 := by
  have hc (i j : Fin 5) (hij : i < j) (hi : i.val < 2) (hj : 2 ≤ j.val) :
      g * root hij = root hij * g :=
    (mem_centralizer_iff.mp hg _ (subset_closure ⟨i,j,hij,hi,hj,rfl⟩)).symm
  have hrow (i j : Fin 5) (hi : 2 ≤ i.val) :
      g i j = if i = j then g 0 0 else 0 := by
    have he := centralizer_root_entry g (by omega : (0 : Fin 5) < i)
      (hc 0 i (by omega) (by decide) hi) 0 j
    simpa only [ite_true, eq_comm] using he
  have h01 := centralizer_root_entry g (by decide : (1 : Fin 5) < 2)
    (hc 1 2 (by decide) (by decide) (by decide)) 0 2
  have h10 := centralizer_root_entry g (by decide : (0 : Fin 5) < 2)
    (hc 0 2 (by decide) (by decide) (by decide)) 1 2
  have h11 := centralizer_root_entry g (by decide : (1 : Fin 5) < 2)
    (hc 1 2 (by decide) (by decide) (by decide)) 1 2
  refine ⟨hrow, ?_, ?_, ?_⟩
  · simpa using h01.symm
  · simpa using h10.symm
  · simpa [hrow 2 2 (by decide)] using h11.symm

/-- The model rectangle is self-centralizing in the full five-dimensional group. -/
theorem model_plane_centralizer_eq : Subgroup.centralizer (Model.plane : Set SL) = Model.plane := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hrow, h01, h10, h11⟩ := centralizer_plane_pattern g hg
    have h00 : g 0 0 = 1 := by
      have hne : g 0 0 ≠ 0 := by
        intro hzero
        apply g.det_ne_zero
        apply Matrix.det_eq_zero_of_row_eq_zero 2
        intro j
        simp [hrow 2 j (by decide), hzero]
      exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hne
    have he : g = planeWord (fun i j => g (i.castLE (by decide)) (j.natAdd 2)) := by
      apply Subtype.ext
      rw [planeWord_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single, hrow, h00, h01, h10, h11]
    rw [he]
    exact planeWord_mem _
  · let := model_rectangle_commutative 2
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy => setLike_mul_comm hy hx
end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
