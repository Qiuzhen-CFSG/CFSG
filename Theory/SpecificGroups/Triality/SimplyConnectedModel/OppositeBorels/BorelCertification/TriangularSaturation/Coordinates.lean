module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.Triangular

/-!
# Signed hyperbolic coordinates for triangular Spin elimination

Exchanging the two hyperbolic halves puts the positive and negative root
operations in the same block coordinates. The natural quadratic isometry
supplies isotropic-column and polar identities; triangular invertibility
supplies nonzero pivots. These facts support the concrete saturation proof.

Source: GLS3 Theorem 1.11.2 and Steinberg (6.2)(a-b),
`refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
open Triality.Standard.PositiveCoordinates
open scoped BigOperators
@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def swapOrder (negative : Bool) : Index ≃ Index :=
  if negative then Equiv.sumComm _ _ else Equiv.refl _

def blockMatrix (negative : Bool) : Points k →* Matrix Index Index k where
  toFun g := (pointMatrix k g).submatrix (swapOrder negative) (swapOrder negative)
  map_one' := by rw [pointMatrix_one]; exact Matrix.submatrix_one_equiv _
  map_mul' g h := by rw [pointMatrix_mul]; exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

omit [CharP k 2] in
lemma blockMatrix_eq (negative : Bool) (g : Points k) :
    blockMatrix k negative g =
      (matrix k negative g).submatrix coordinateOrder.symm coordinateOrder.symm := by
  ext p q
  cases negative <;> simp [blockMatrix, matrix, signedOrder, swapOrder]

lemma blockMatrix_injective (negative : Bool) : Function.Injective (blockMatrix k negative) := by
  intro g h heq
  apply pointMatrix_injective k
  ext p q
  have h := congrFun (congrFun heq ((swapOrder negative).symm p)) ((swapOrder negative).symm q)
  simpa [blockMatrix] using h

omit [CharP k 2] in
lemma triangular_blocks (negative : Bool) (g : Points k)
    (hg : tTriangular 8 (matrix k negative g)) :
    (∀ i j : Fin 4, j < i → blockMatrix k negative g (.inl i) (.inl j) = 0) ∧
    (∀ i j : Fin 4, blockMatrix k negative g (.inr i) (.inl j) = 0) := by
  rw [blockMatrix_eq]
  constructor
  · intro i j hij
    apply hg
    change j.val < i.val
    exact hij
  · intro i j
    apply hg
    fin_cases i <;> fin_cases j <;> decide

omit [CharP k 2] in
lemma diagonal_ne_zero (negative : Bool) (g : Points k)
    (hg : tTriangular 8 (matrix k negative g)) (i : Index) :
    blockMatrix k negative g i i ≠ 0 := by
  have hu : IsUnit (matrix k negative g) := (linear k negative g).isUnit
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_of_isUpperTriangular hg] at hd
  have hn := Finset.prod_ne_zero_iff.mp hd.ne_zero (coordinateOrder.symm i) (Finset.mem_univ _)
  simpa [blockMatrix_eq] using hn

lemma difference_matrix (negative : Bool) (i j : Fin 4) (hij : i < j) (a : k) :
    blockMatrix k negative (rootPoint k (signedRoot negative (difference i j hij)) a) =
      1 + Matrix.single (.inl i) (.inl j) a + Matrix.single (.inr j) (.inr i) a := by
  cases negative <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
  · change (pointMatrix k _).submatrix _ _ = _
    rw [root_difference_matrix]
    rfl
  · change (pointMatrix k _).submatrix _ _ = _
    rw [root_negative_difference_matrix]
    ext p q
    cases p <;> cases q <;>
      simp [Matrix.submatrix_apply, Matrix.add_apply, swapOrder, Matrix.one_apply,
        Matrix.single_apply, add_comm, add_left_comm, add_assoc]

lemma sum_matrix (negative : Bool) (i j : Fin 4) (hij : i < j) (a : k) :
    blockMatrix k negative (rootPoint k (signedRoot negative (sumRoot i j hij)) a) =
      1 + Matrix.single (.inl i) (.inr j) a + Matrix.single (.inl j) (.inr i) a := by
  cases negative <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
  · change (pointMatrix k _).submatrix _ _ = _
    rw [root_sum_matrix]
    rfl
  · change (pointMatrix k _).submatrix _ _ = _
    rw [root_negative_sum_matrix]
    ext p q
    cases p <;> cases q <;>
      simp [Matrix.submatrix_apply, Matrix.add_apply, swapOrder, Matrix.one_apply,
        Matrix.single_apply]

omit [CharP k 2] in
private lemma point_isotropic (g : Points k) (q : Index) :
    ∑ i : Fin 4, pointMatrix k g (.inl i) q * pointMatrix k g (.inr i) q = 0 := by
  simp only [pointMatrix_apply, basis_coord_inl, basis_coord_inr]
  rw [← hyperbolicForm_apply]
  rw [(mem_quadraticIsometrySubgroup _ _).1 (naturalAction k g).2]
  cases q <;> simp [basis_apply, quadraticForm, hyperbolicForm_apply]

omit [CharP k 2] in
lemma isotropic (negative : Bool) (g : Points k) (q : Index) :
    ∑ i : Fin 4, blockMatrix k negative g (.inl i) q *
      blockMatrix k negative g (.inr i) q = 0 := by
  cases negative
  · exact point_isotropic k g q
  · simpa [blockMatrix, swapOrder, mul_comm] using point_isotropic k g (Sum.swap q)

omit [CharP k 2] in
private lemma point_polar (g : Points k) (p q : Index) :
    ∑ i : Fin 4, (pointMatrix k g (.inl i) p * pointMatrix k g (.inr i) q +
      pointMatrix k g (.inl i) q * pointMatrix k g (.inr i) p) =
        if p = Sum.swap q then 1 else 0 := by
  have hQ (v : QuadraticSpace k) : quadraticForm k ((naturalAction k g).1 v) = quadraticForm k v :=
    (mem_quadraticIsometrySubgroup _ _).1 (naturalAction k g).2 v
  have hp (x y : QuadraticSpace k) :
      (quadraticForm k).polarBilin ((naturalAction k g).1 x) ((naturalAction k g).1 y) =
        (quadraticForm k).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hQ]
  simp only [pointMatrix_apply, basis_coord_inl, basis_coord_inr]
  rw [← hyperbolicForm_polar, hp]
  change (hyperbolicForm (k := k) 4).polarBilin (basis k p) (basis k q) = _
  rw [hyperbolicForm_polar]
  cases p <;> cases q <;>
    simp [basis_apply, Pi.single_apply, eq_comm]

omit [CharP k 2] in
lemma polar (negative : Bool) (g : Points k) (p q : Index) :
    ∑ i : Fin 4, (blockMatrix k negative g (.inl i) p * blockMatrix k negative g (.inr i) q +
      blockMatrix k negative g (.inl i) q * blockMatrix k negative g (.inr i) p) =
        if p = Sum.swap q then 1 else 0 := by
  cases negative
  · exact point_polar k g p q
  · have he : Sum.swap p = q ↔ p = Sum.swap q := by
      constructor <;> intro h <;> simpa using congrArg Sum.swap h
    simpa [blockMatrix, swapOrder, mul_comm, add_comm, he] using
      point_polar k g (Sum.swap p) (Sum.swap q)

lemma signed_root_mem (negative : Bool) (r : Fin 12) (a : k) :
    rootPoint k (signedRoot negative (rootIndex r)) a ∈ unipotent k negative := by
  apply rootPoint_mem_rootGenerated
  cases negative
  · exact rootIndex_positive r
  · change (pinnedRootData k).neg (pinnedRootIndex k (negativeRoot (rootIndex r))) ∈ positiveRoots k
    rw [pinnedRootData_neg, negativeRoot_negativeRoot]
    exact rootIndex_positive r

lemma difference_mem (negative : Bool) (i j : Fin 4) (hij : i < j) (a : k) :
    rootPoint k (signedRoot negative (difference i j hij)) a ∈ unipotent k negative := by
  have he : ∃ r, rootIndex r = difference i j hij := by
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij <;>
      first
      | exact ⟨0, rfl⟩
      | exact ⟨1, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩
      | exact ⟨7, rfl⟩
  obtain ⟨r, hr⟩ := he
  rw [← hr]
  exact signed_root_mem k negative r a

lemma sum_mem (negative : Bool) (i j : Fin 4) (hij : i < j) (a : k) :
    rootPoint k (signedRoot negative (sumRoot i j hij)) a ∈ unipotent k negative := by
  have he : ∃ r, rootIndex r = sumRoot i j hij := by
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij <;>
      first
      | exact ⟨2, rfl⟩
      | exact ⟨6, rfl⟩
      | exact ⟨8, rfl⟩
      | exact ⟨9, rfl⟩
      | exact ⟨10, rfl⟩
      | exact ⟨11, rfl⟩
  obtain ⟨r, hr⟩ := he
  rw [← hr]
  exact signed_root_mem k negative r a

end Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
