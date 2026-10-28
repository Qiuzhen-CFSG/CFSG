module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Bivectors
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Shears
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases

/-!
# The stabilizer of the nonsimple binary bivector

The stabilizer of e₀∧e₁ + e₂∧e₃ in SL₅(2) restricts onto Sp₄(2) on its
support Γ₄. The basis (e₀,e₂,e₁,e₃) identifies the coefficient matrix with
Mathlib's standard symplectic matrix J. In these coordinates every stabilizer
matrix has blocks [A u; 0 1], with A symplectic. Conversely [A 0; 0 1] gives
a multiplicative section. The restriction kernel consists exactly of the
shared last-column shears, so it is normal in this stabilizer.

Composing the resulting quotient equivalence with the inverse of the faithful
six-letter polar representation gives the actual S₆ quotient. This proves the
stabilizer calculation in Aschbacher–Smith, *The Classification of Quasithin
Groups*, 12.5.5(3), printed p.819/PDF p.836. Identifying the shared shear
subgroup with the independently defined source radical R₆ is a separate result.
-/

@[expose] public section

open scoped Matrix
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
namespace StabilizerCoordinates

abbrev I := Fin 2 ⊕ Fin 2
abbrev E := I ⊕ Fin 1

/-- Coordinates (e₀,e₂,e₁,e₃;e₄), matching the two halves of Matrix.J. -/
def index : E ≃ Fin 5 where
  toFun := Sum.elim (Sum.elim (fun i => ![0,2] i) (fun i => ![1,3] i)) (fun _ => 4)
  invFun i := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inr 0),
    Sum.inl (Sum.inl 1), Sum.inl (Sum.inr 1), Sum.inr 0] i
  left_inv i := by
    rcases i with (i | i) | i <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Simultaneous row and column transport to the symplectic block coordinates. -/
def reindex : Matrix (Fin 5) (Fin 5) (ZMod 2) ≃+* Matrix E E (ZMod 2) :=
  Matrix.reindexRingEquiv (ZMod 2) index.symm

@[simp] theorem reindex_transpose (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    reindex A.transpose = (reindex A).transpose := rfl

@[simp] theorem det_reindex (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    (reindex A).det = A.det := Matrix.det_submatrix_equiv_self _ _

@[simp] theorem det_reindex_symm (A : Matrix E E (ZMod 2)) :
    (reindex.symm A).det = A.det := Matrix.det_submatrix_equiv_self _ _

/-- The displayed bivector restricts to the exact standard symplectic form. -/
theorem form : reindex (bivectorMatrix nondecomposable) =
    Matrix.fromBlocks (Matrix.J (Fin 2) (ZMod 2)) 0 0 (0 : Matrix (Fin 1) (Fin 1) _) := by
  rw [bivectorMatrix, coordinates_nondecomposable]
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [reindex, Matrix.reindexRingEquiv, Matrix.reindexAddEquiv, Matrix.reindex_apply,
      index, alternatingMatrix, Matrix.J,
      Matrix.fromBlocks, ZMod.neg_eq_self_mod_two]

/-- The actual ambient matrix in the reordered coordinates. -/
noncomputable def matrix (g : Group) := reindex g.val

@[simp] theorem matrix_mul (g h : Group) : matrix (g * h) = matrix g * matrix h :=
  map_mul reindex g.val h.val

@[simp] theorem matrix_one : matrix 1 = 1 := map_one reindex

theorem preserves_form (g : nondecomposableStabilizer) :
    matrix g.val * Matrix.fromBlocks (Matrix.J (Fin 2) (ZMod 2)) 0 0
      (0 : Matrix (Fin 1) (Fin 1) _) * (matrix g.val).transpose =
      Matrix.fromBlocks (Matrix.J (Fin 2) (ZMod 2)) 0 0 (0 : Matrix (Fin 1) (Fin 1) _) := by
  have h := congrArg reindex (bivectorMatrix_action g.val nondecomposable)
  rw [g.property, map_mul, map_mul, reindex_transpose, form] at h
  exact h.symm

/-- The restriction to the support preserves the standard symplectic matrix. -/
theorem block_symplectic (g : nondecomposableStabilizer) :
    (matrix g.val).toBlocks₁₁ ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
  apply SymplecticGroup.mem_iff.mpr
  have h := congrArg Matrix.toBlocks₁₁ (preserves_form g)
  conv_lhs at h => rw [← Matrix.fromBlocks_toBlocks (matrix g.val)]
  simpa [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose] using h

theorem lower_zero (g : nondecomposableStabilizer) :
    (matrix g.val).toBlocks₂₁ = 0 := by
  have hp := nondecomposableStabilizer_le_parabolic_four g.property
  have hz (j : Fin 5) (hj : j.val < 4) : g.val.val 4 j = 0 := by
    have hv : Pi.single j (1 : ZMod 2) ∈ naturalFlag 4 := by
      intro l hl
      have hn : l ≠ j := by intro he; subst l; omega
      simp [hn]
    have hh := (hp _).mpr hv 4 (by decide)
    change g.val.val.mulVec (Pi.single j 1) 4 = 0 at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  ext i j
  fin_cases i
  rcases j with j | j <;> fin_cases j <;> exact hz _ (by decide)

/-- Stabilizer matrices have a symplectic block, an arbitrary shear column,
and identity action on the one-dimensional binary quotient. -/
theorem blocks (g : nondecomposableStabilizer) :
    matrix g.val = Matrix.fromBlocks (matrix g.val).toBlocks₁₁
      (matrix g.val).toBlocks₁₂ 0 1 := by
  have hd : (matrix g.val).det = 1 := (det_reindex _).trans g.val.property
  have hb := Matrix.fromBlocks_toBlocks (matrix g.val)
  rw [lower_zero g] at hb
  rw [← hb, Matrix.det_fromBlocks_zero₂₁,
    SymplecticGroup.det_eq_one (block_symplectic g), one_mul] at hd
  have hlast : (matrix g.val).toBlocks₂₂ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_unique] using hd
  simpa only [hlast] using hb.symm

/-- Extend a symplectic transformation by the identity on e₄. -/
noncomputable def lift (A : Matrix.symplecticGroup (Fin 2) (ZMod 2)) : Group :=
  ⟨reindex.symm (Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) _)), by
    rw [det_reindex_symm, Matrix.det_fromBlocks_zero₂₁,
      SymplecticGroup.det_eq_one A.property, Matrix.det_one, mul_one]⟩

@[simp] theorem matrix_lift (A : Matrix.symplecticGroup (Fin 2) (ZMod 2)) :
    matrix (lift A) = Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin 1) (Fin 1) _) :=
  reindex.apply_symm_apply _

theorem lift_mem (A : Matrix.symplecticGroup (Fin 2) (ZMod 2)) :
    lift A ∈ nondecomposableStabilizer := by
  apply bivectorMatrix_injective
  rw [bivectorMatrix_action]
  apply reindex.injective
  rw [map_mul, map_mul, reindex_transpose, form]
  change matrix (lift A) * _ * (matrix (lift A)).transpose = _
  rw [matrix_lift]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
    SymplecticGroup.mem_iff.mp A.property]

noncomputable def liftHom : Matrix.symplecticGroup (Fin 2) (ZMod 2) →* Group where
  toFun := lift
  map_one' := by
    apply Subtype.ext
    apply reindex.injective
    change matrix (lift 1) = matrix 1
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply reindex.injective
    change matrix (lift (A * B)) = matrix (lift A * lift B)
    simp [Matrix.fromBlocks_multiply]

def column (u : ShearParameter) : Matrix I (Fin 1) (ZMod 2) :=
  fun i _ => Sum.elim (fun j => ![u 0, u 2] j) (fun j => ![u 1, u 3] j) i

theorem matrix_shear_blocks (u : ShearParameter) :
    matrix (shear u) = Matrix.fromBlocks 1 (column u) 0 1 := by
  unfold matrix
  rw [matrix_shear]
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    fin_cases i <;> fin_cases j <;> rfl

end StabilizerCoordinates

open StabilizerCoordinates

/-- The genuine restriction homomorphism on the support of the bivector. -/
noncomputable def nondecomposableToSymplectic :
    nondecomposableStabilizer →* Matrix.symplecticGroup (Fin 2) (ZMod 2) where
  toFun g := ⟨(matrix g.val).toBlocks₁₁, block_symplectic g⟩
  map_one' := by
    apply Subtype.ext
    change (matrix 1).toBlocks₁₁ = 1
    rw [matrix_one]
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    change (matrix (g.val * h.val)).toBlocks₁₁ =
      (matrix g.val).toBlocks₁₁ * (matrix h.val).toBlocks₁₁
    rw [matrix_mul, blocks g, blocks h]
    simp [Matrix.fromBlocks_multiply]

/-- Restriction to Γ₄ in the ordered symplectic basis (e₀,e₂,e₁,e₃). -/
theorem nondecomposableToSymplectic_apply (g : nondecomposableStabilizer)
    (i j : Fin 2 ⊕ Fin 2) :
    (nondecomposableToSymplectic g).val i j =
      g.val.val (StabilizerCoordinates.index (Sum.inl i))
        (StabilizerCoordinates.index (Sum.inl j)) := rfl

/-- A split section given by block-diagonal symplectic transformations. -/
noncomputable def nondecomposableSymplecticSection :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) →* nondecomposableStabilizer :=
  liftHom.codRestrict nondecomposableStabilizer lift_mem

@[simp] theorem nondecomposableToSymplectic_section
    (A : Matrix.symplecticGroup (Fin 2) (ZMod 2)) :
    nondecomposableToSymplectic (nondecomposableSymplecticSection A) = A := by
  apply Subtype.ext
  change (matrix (lift A)).toBlocks₁₁ = A.val
  rw [matrix_lift, Matrix.toBlocks_fromBlocks₁₁]

theorem nondecomposableToSymplectic_surjective :
    Function.Surjective nondecomposableToSymplectic :=
  fun A => ⟨nondecomposableSymplecticSection A, nondecomposableToSymplectic_section A⟩

/-- The kernel is exactly the shared shear subgroup, taken inside the stabilizer. -/
theorem nondecomposableToSymplectic_ker :
    nondecomposableToSymplectic.ker = shearSubgroup.subgroupOf nondecomposableStabilizer := by
  ext g
  change nondecomposableToSymplectic g = 1 ↔ g.val ∈ shearSubgroup
  rw [mem_shearSubgroup]
  constructor
  · intro hg
    have ht : (matrix g.val).toBlocks₁₁ = 1 := congrArg Subtype.val hg
    let u : ShearParameter := fun i => g.val.val i.castSucc 4
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply reindex.injective
    change matrix (shear u) = matrix g.val
    rw [matrix_shear_blocks, blocks g, ht]
    congr 1
    ext i j
    rcases i with i | i <;> fin_cases i <;> fin_cases j <;> rfl
  · rintro ⟨u, hu⟩
    apply Subtype.ext
    change (matrix g.val).toBlocks₁₁ = 1
    rw [← hu, matrix_shear_blocks, Matrix.toBlocks_fromBlocks₁₁]

/-- Normality is relative to the bivector stabilizer. -/
instance nondecomposable_shear_normal :
    (shearSubgroup.subgroupOf nondecomposableStabilizer).Normal := by
  rw [← nondecomposableToSymplectic_ker]
  infer_instance

/-- The six-letter action obtained from the actual symplectic restriction. -/
noncomputable def nondecomposableToSymmetricSix :
    nondecomposableStabilizer →* Equiv.Perm (Fin 6) :=
  Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp
    nondecomposableToSymplectic

theorem nondecomposableToSymmetricSix_surjective :
    Function.Surjective nondecomposableToSymmetricSix :=
  Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.surjective.comp
    nondecomposableToSymplectic_surjective

theorem nondecomposableToSymmetricSix_ker :
    nondecomposableToSymmetricSix.ker =
      shearSubgroup.subgroupOf nondecomposableStabilizer := by
  rw [nondecomposableToSymmetricSix, MonoidHom.ker_comp_of_injective _ _
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective]
  exact nondecomposableToSymplectic_ker

/-- The quotient of the literal stabilizer by its relative shear subgroup. -/
noncomputable def nondecomposableQuotientEquivSymplectic :
    (nondecomposableStabilizer ⧸ shearSubgroup.subgroupOf nondecomposableStabilizer) ≃*
      Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq nondecomposableToSymplectic_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective nondecomposableToSymplectic
      nondecomposableToSymplectic_surjective)

/-- The stabilizer extension in Aschbacher–Smith 12.5.5(3), with the shared
shear subgroup as kernel. Its identification with source R₆ is independent. -/
noncomputable def nondecomposableQuotientEquivSymmetricSix :
    (nondecomposableStabilizer ⧸ shearSubgroup.subgroupOf nondecomposableStabilizer) ≃*
      Equiv.Perm (Fin 6) :=
  nondecomposableQuotientEquivSymplectic.trans
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm

@[simp] theorem nondecomposableQuotientEquivSymmetricSix_mk
    (g : nondecomposableStabilizer) :
    nondecomposableQuotientEquivSymmetricSix (QuotientGroup.mk g) =
      nondecomposableToSymmetricSix g := rfl

end Representation.SL5ExteriorSquare
