module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Coordinates for the graph-field fixed matrices

Reindexing the native symplectic basis gives an injective homomorphism to
GL₄ with the prescribed matrix formula. Its fixed-subgroup image is described
by preservation of the antidiagonal form and sixteen explicit exterior-square
minor equations. This provides a common matrix interface for the Suzuki
coordinate calculations, including the binary field.

Source: Aschbacher--Smith, 16.1.4(7), printed p.1171; the exterior-square
construction is from GLS3, Theorem 2.5.1, as implemented in
`ExceptionalGraph.Construction`.
-/

@[expose] public noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
open ExceptionalGraph BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
variable {F : Type*} [Field F]

/-- The actual symplectic embedding in Suzuki coordinates. -/
def coordinatesGL : Sp F →* GL (Fin 4) F :=
  ((Matrix.reindexRingEquiv F suzukiIndex).toMonoidHom.comp
    (Matrix.symplecticGroup (Fin 2) F).subtype).toHomUnits

theorem coordinatesGL_val (g : Sp F) :
    (coordinatesGL g).val = matrixCoordinates (RingEquiv.refl F) g := rfl

/-- Return a Suzuki-coordinate matrix to the native symplectic basis. -/
def nativeMatrix (M : Matrix (Fin 4) (Fin 4) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  M.submatrix suzukiIndex suzukiIndex

/-- The alternating form in Suzuki coordinates, in characteristic two. -/
def suzukiForm : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]

theorem nativeMatrix_form [CharP F 2] : nativeMatrix (suzukiForm : Matrix _ _ F) =
    Matrix.J (Fin 2) F := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [nativeMatrix, suzukiForm, suzukiIndex, Matrix.J, Matrix.fromBlocks, CharTwo.neg_eq]

theorem nativeMatrix_symplectic_iff [CharP F 2] (M : Matrix (Fin 4) (Fin 4) F) :
    nativeMatrix M ∈ Matrix.symplecticGroup (Fin 2) F ↔
      M * suzukiForm * M.transpose = suzukiForm := by
  rw [SymplecticGroup.mem_iff, ← nativeMatrix_form]
  change (M.submatrix suzukiIndex suzukiIndex) *
    (suzukiForm.submatrix suzukiIndex suzukiIndex) *
    (M.submatrix suzukiIndex suzukiIndex).transpose =
      suzukiForm.submatrix suzukiIndex suzukiIndex ↔ _
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  constructor
  · intro h
    ext i j
    have hh := congrArg (fun N => N (suzukiIndex.symm i) (suzukiIndex.symm j)) h
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hh
  · intro h
    rw [h]

def coordinateFirst : Fin 4 → Fin 4 := ![0, 0, 1, 3]
def coordinateSecond : Fin 4 → Fin 4 := ![1, 2, 3, 2]
/-- The exterior-square minor formula in Suzuki coordinates. -/
def coordinateGraph (M : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  fun i j => M (coordinateFirst i) (coordinateFirst j) *
      M (coordinateSecond i) (coordinateSecond j) +
    M (coordinateFirst i) (coordinateSecond j) *
      M (coordinateSecond i) (coordinateFirst j)

theorem nativeMatrix_graph (M : Matrix (Fin 4) (Fin 4) F) :
    nativeMatrix (coordinateGraph M) = graphMatrix (nativeMatrix M) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> rfl

theorem coordinatesGL_injective : Function.Injective (coordinatesGL (F := F)) := by
  intro g h he
  exact matrixCoordinates_injective (RingEquiv.refl _) (congrArg Units.val he)

theorem coordinatesGL_native (A : GL (Fin 4) F)
    (hA : nativeMatrix A.val ∈ Matrix.symplecticGroup (Fin 2) F) :
    coordinatesGL ⟨nativeMatrix A.val, hA⟩ = A := by
  apply Units.ext
  ext i j
  simp [coordinatesGL_val, matrixCoordinates, nativeMatrix]

omit [Field F] in
theorem nativeMatrix_injective : Function.Injective (nativeMatrix (F := F)) := by
  intro M N h
  ext i j
  have hh := congrArg (fun P => P (suzukiIndex.symm i) (suzukiIndex.symm j)) h
  simpa only [nativeMatrix, Matrix.submatrix_apply, Equiv.apply_symm_apply] using hh

theorem nativeMatrix_coordinates (g : Sp F) :
    nativeMatrix (matrixCoordinates (RingEquiv.refl F) g) = g.val := by
  ext i j
  simp [nativeMatrix, matrixCoordinates]

variable [Finite F] [CharP F 2]
/-- The image of the genuine fixed symplectic subgroup in GL₄. -/
def fixedMatrixSubgroup (m : ℕ) : Subgroup (GL (Fin 4) F) :=
  (graphFieldAut (F := F) m).fixedSubgroup.map coordinatesGL

/-- Membership is precisely the symplectic equation and the twisted minor equation. -/
theorem mem_fixedMatrixSubgroup_iff (m : ℕ) (A : GL (Fin 4) F) :
    A ∈ fixedMatrixSubgroup m ↔
      A.val * suzukiForm * A.val.transpose = suzukiForm ∧
      coordinateGraph A.val = A.val.map (iterateFrobeniusEquiv F 2 (m + 1)) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    constructor
    · rw [← nativeMatrix_symplectic_iff, coordinatesGL_val, nativeMatrix_coordinates]
      exact g.property
    · apply nativeMatrix_injective
      rw [nativeMatrix_graph, coordinatesGL_val, nativeMatrix_coordinates]
      have he := (mem_fixed_iff m g).mp hg
      convert he using 1
      ext i j
      simp [nativeMatrix, matrixCoordinates]
  · rintro ⟨hsp, hfix⟩
    let g : Sp F := ⟨nativeMatrix A.val, (nativeMatrix_symplectic_iff A.val).mpr hsp⟩
    refine ⟨g, ?_, coordinatesGL_native A g.property⟩
    apply (mem_fixed_iff m g).mpr
    change graphMatrix (nativeMatrix A.val) = _
    rw [← nativeMatrix_graph, hfix]
    rfl

theorem mem_fixedMatrixSubgroup_coordinatesGL_iff (m : ℕ) (g : Sp F) :
    coordinatesGL g ∈ fixedMatrixSubgroup m ↔ g ∈ (graphFieldAut m).fixedSubgroup := by
  constructor
  · rintro ⟨h, hh, he⟩
    exact coordinatesGL_injective he ▸ hh
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- Reindexing is an equivalence onto the concrete image of the fixed subgroup. -/
def fixedCoordinatesEquiv (m : ℕ) :
    (graphFieldAut (F := F) m).fixedSubgroup ≃* fixedMatrixSubgroup (F := F) m :=
  (graphFieldAut m).fixedSubgroup.equivMapOfInjective coordinatesGL coordinatesGL_injective

@[simp] theorem fixedCoordinatesEquiv_val (m : ℕ)
    (g : (graphFieldAut (F := F) m).fixedSubgroup) :
    (fixedCoordinatesEquiv m g).val = coordinatesGL g.val := rfl

/-- The coefficient field used by the actual Suzuki generators. -/
abbrev SuzukiField (m : ℕ) := BinaryGaloisField (2 * m + 1)

/-- The Tits automorphism, including the identity automorphism at `m = 0`. -/
def suzukiTheta (m : ℕ) : SuzukiField m ≃+* SuzukiField m :=
  iterateFrobeniusEquiv (SuzukiField m) 2 (m + 1)

theorem suzukiTheta_apply (m : ℕ) (x : SuzukiField m) :
    suzukiTheta m x = x ^ (2 ^ (m + 1)) :=
  iterateFrobeniusEquiv_def _ _ _ _

theorem suzukiField_pow_card (m : ℕ) (x : SuzukiField m) :
    x ^ (2 ^ (2 * m + 1)) = x := by
  let := Fintype.ofFinite (SuzukiField m)
  rw [← GaloisField.card 2 (2 * m + 1) (by omega), Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The Tits automorphism squares to Frobenius for every parameter. -/
theorem suzukiTheta_twice (m : ℕ) (x : SuzukiField m) :
    suzukiTheta m (suzukiTheta m x) = x ^ 2 := by
  rw [suzukiTheta_apply, suzukiTheta_apply, ← pow_mul, ← pow_add]
  rw [show m + 1 + (m + 1) = (2 * m + 1) + 1 by omega,
    pow_succ, pow_mul, suzukiField_pow_card]

/-- The inverse Tits power used in the diagonal generators. -/
theorem suzukiTheta_half (m : ℕ) (x : SuzukiField m) :
    suzukiTheta m (x ^ (2 ^ m)) = x := by
  rw [suzukiTheta_apply, ← pow_mul, ← pow_add,
    show m + (m + 1) = 2 * m + 1 by omega, suzukiField_pow_card]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
