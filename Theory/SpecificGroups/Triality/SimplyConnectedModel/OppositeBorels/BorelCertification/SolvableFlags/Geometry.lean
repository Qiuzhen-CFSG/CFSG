module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.Triangular
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.Linear

/-!
# The two middle choices give the same orthogonal triangular support

Initial spans of the signed hyperbolic basis, and of the basis with positions
3 and 4 interchanged, define the two possible coordinate flags. An isometry
preserving the second flag has at most one extra lower matrix entry. Its
isotropic fourth column and nonzero diagonal kill that entry. Thus either
flag forces the prescribed triangular support, for both choices of sign.

This is the linear stabilizer step in GLS3, 1.11.2
(`refs/KGroup/GLS3/Chapter1.tex`) and Steinberg (6.2)(a)
(`refs/KGroup/GLS3/Chapter2St2.tex`). No flag uniqueness is assumed.
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
open Theory.AlgebraicGroup.BorelGeometricConjugacy
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
universe u
variable (k : Type u) [Field k]

def orderedBasis (e : Fin 8 ≃ Index) : Module.Basis (Fin 8) k (QuadraticSpace k) :=
  (basis k).reindex e.symm

lemma orderedBasis_apply (e : Fin 8 ≃ Index) (i : Fin 8) :
    orderedBasis k e i = basis k (e i) := by simp [orderedBasis]

lemma finrank_quadraticSpace : Module.finrank k (QuadraticSpace k) = 8 := by
  exact Module.finrank_eq_card_basis (orderedBasis k coordinateOrder)

def coordinateFlag (e : Fin 8 ≃ Index) : FullFlag k (QuadraticSpace k) where
  subspace r := Submodule.span k
    (Set.range fun j : Fin (min r 8) => orderedBasis k e (Fin.castLE (min_le_right _ _) j))
  monotone := by
    intro i j hij
    apply Submodule.span_mono
    rintro x ⟨l, rfl⟩
    exact ⟨⟨l, lt_of_lt_of_le l.isLt (min_le_min_right _ hij)⟩, rfl⟩
  finrank_eq r := by
    have hli : LinearIndependent k (fun j : Fin (min r 8) =>
        orderedBasis k e (Fin.castLE (min_le_right _ _) j)) :=
      (orderedBasis k e).linearIndependent.comp
        (Fin.castLE (min_le_right r 8)) (Fin.castLE_injective _)
    rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_quadraticSpace]

lemma mem_coordinateFlag (e : Fin 8 ≃ Index) (r : ℕ) (v : QuadraticSpace k) :
    v ∈ (coordinateFlag k e).subspace r ↔
      ∀ i : Fin 8, r ≤ i.val → (basis k).coord (e i) v = 0 := by
  have h := basisSpanCoord (QuadraticSpace k) 8 (orderedBasis k e)
    (min r 8) (min_le_right _ _) ((orderedBasis k e).equivFun v)
  simp only [LinearEquiv.symm_apply_apply] at h
  simpa [coordinateFlag, Module.Basis.coord_apply,
    Module.Basis.equivFun_apply, orderedBasis, Module.Basis.repr_reindex_apply,
    min_le_iff, not_le.mpr (Fin.isLt _)] using h

lemma orderedBasis_mem_coordinateFlag (e : Fin 8 ≃ Index) (i : Fin 8) :
    orderedBasis k e i ∈ (coordinateFlag k e).subspace (i.val + 1) := by
  apply Submodule.subset_span
  exact ⟨⟨i.val, lt_min (Nat.lt_succ_self _) i.isLt⟩, rfl⟩

variable [IsAlgClosed k]

lemma triangular_of_preserves_coordinateFlag (e : Fin 8 ≃ Index) (g : Points k)
    (h : ∀ r v, v ∈ (coordinateFlag k e).subspace r →
      (naturalAction k g).1 v ∈ (coordinateFlag k e).subspace r) :
    tTriangular 8 ((pointMatrix k g).submatrix e e) := by
  intro i j hij
  simpa only [Matrix.submatrix_apply, pointMatrix_apply, orderedBasis_apply] using
    (mem_coordinateFlag k e (j.val + 1) _).mp
      (h _ _ (orderedBasis_mem_coordinateFlag k e j)) i (by omega)

def middleSwap : Equiv.Perm (Fin 8) := Equiv.swap 3 4

def flagOrder (negative alternate : Bool) : Fin 8 ≃ Index :=
  (if alternate then middleSwap else Equiv.refl _).trans (signedOrder negative)

private lemma swap_lt (i j : Fin 8) (h : j < i) (he : ¬ (i = 4 ∧ j = 3)) :
    middleSwap j < middleSwap i := by
  have hh : ∀ i j : Fin 8, j < i → ¬ (i = 4 ∧ j = 3) →
      middleSwap j < middleSwap i := by decide
  exact hh i j h he

omit [IsAlgClosed k] in
private lemma swapped_triangular_entry (M : Matrix (Fin 8) (Fin 8) k)
    (hM : tTriangular 8 (M.submatrix middleSwap middleSwap))
    (i j : Fin 8) (hij : j < i) (he : ¬ (i = 4 ∧ j = 3)) : M i j = 0 := by
  have h := hM (swap_lt i j hij he)
  simpa [Matrix.submatrix_apply, middleSwap] using h

lemma matrix_isotropic_column (negative : Bool) (g : Points k) (j : Fin 8) :
    matrix k negative g 0 j * matrix k negative g 7 j +
      matrix k negative g 1 j * matrix k negative g 6 j +
      matrix k negative g 2 j * matrix k negative g 5 j +
      matrix k negative g 3 j * matrix k negative g 4 j = 0 := by
  have h := (mem_quadraticIsometrySubgroup _ _).mp (naturalAction k g).property
    (basis k (signedOrder negative j))
  have hz : quadraticForm k (basis k (signedOrder negative j)) = 0 := by
    cases signedOrder negative j <;> simp [basis_apply, quadraticForm, hyperbolicForm_apply]
  rw [hz] at h
  simp only [matrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.submatrix_apply,
    pointMatrix_apply]
  generalize (naturalAction k g).1 (basis k (signedOrder negative j)) = v at h ⊢
  simp only [quadraticForm, hyperbolicForm_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero] at h
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl] at h
  cases negative
  · change v.1 0 * v.2 0 + v.1 1 * v.2 1 + v.1 2 * v.2 2 + v.1 3 * v.2 3 = 0
    simpa only [add_assoc] using h
  · change v.2 0 * v.1 0 + v.2 1 * v.1 1 + v.2 2 * v.1 2 + v.2 3 * v.1 3 = 0
    simpa only [add_assoc, mul_comm] using h

lemma triangular_of_swapped_triangular (negative : Bool) (g : Points k)
    (h : tTriangular 8
      ((matrix k negative g).submatrix middleSwap middleSwap)) :
    tTriangular 8 (matrix k negative g) := by
  let M := matrix k negative g
  have hdiag : M 3 3 ≠ 0 := by
    have hd : (M.submatrix middleSwap middleSwap).det ≠ 0 := by
      rw [Matrix.det_submatrix_equiv_self]
      have hm : M * matrix k negative g⁻¹ = 1 := by
        change matrix k negative g * matrix k negative g⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one]
      have hd := congrArg Matrix.det hm
      rw [Matrix.det_mul, Matrix.det_one] at hd
      exact left_ne_zero_of_mul_eq_one hd
    rw [det_eq_prod_diagonal_of_tTriangular 8 h] at hd
    have hi := Finset.prod_ne_zero_iff.mp hd (4 : Fin 8) (Finset.mem_univ _)
    simpa [Matrix.submatrix_apply, middleSwap] using hi
  have hmid : M 4 3 = 0 := by
    have hz := matrix_isotropic_column k negative g 3
    change M 0 3 * M 7 3 + M 1 3 * M 6 3 + M 2 3 * M 5 3 + M 3 3 * M 4 3 = 0 at hz
    rw [swapped_triangular_entry k M h 7 3 (by decide) (by decide),
      swapped_triangular_entry k M h 6 3 (by decide) (by decide),
      swapped_triangular_entry k M h 5 3 (by decide) (by decide)] at hz
    exact (mul_eq_zero.mp (by simpa using hz)).resolve_left hdiag
  intro i j hij
  by_cases he : i = 4 ∧ j = 3
  · rcases he with ⟨rfl, rfl⟩; exact hmid
  · exact swapped_triangular_entry k M h i j hij he

lemma triangular_of_preserves_flagOrder (negative alternate : Bool) (g : Points k)
    (h : ∀ r v, v ∈ (coordinateFlag k (flagOrder negative alternate)).subspace r →
      (naturalAction k g).1 v ∈ (coordinateFlag k (flagOrder negative alternate)).subspace r) :
    tTriangular 8 (matrix k negative g) := by
  have ht := triangular_of_preserves_coordinateFlag k (flagOrder negative alternate) g h
  cases alternate with
  | false => simpa [matrix, flagOrder] using ht
  | true => exact triangular_of_swapped_triangular k negative g ht

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
