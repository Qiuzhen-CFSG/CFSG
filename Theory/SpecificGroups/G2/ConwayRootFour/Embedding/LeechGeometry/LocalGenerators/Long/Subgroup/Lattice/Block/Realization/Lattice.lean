module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Arithmetic

/-!
# Faithful integral action on the glued quaternion lattice

The displayed rational basis defines a genuine integral lattice by its image
of `ℤ²⁴`. Integer coordinate identities prove that both source generators and
their inverses preserve it. The source row-Gram identities prove preservation
of the rational form. Subgroup closure then constructs a faithful homomorphism
from the literal `matrixGroup` into this lattice's isometry group.

The identification with the retained Leech lattice is not asserted here;
`Comparison` consumes that independent two-sided integral isometry.
The source matrices are John Bray's ATLAS `6L34G1-Ar6aB0`, and the explicit
quaternion lattice basis is described in `LatticeData`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

theorem basis_mul_inverse : basisMatrix * basisInverse.map (Int.castRingHom ℚ) = 1 := by
  have h := congrArg integerMatrix basis_mul_inverse_integer
  simp only [map_mul, map_ofNat] at h
  change basisNumerator.map (Int.castRingHom ℚ) * basisInverse.map (Int.castRingHom ℚ) = 2 at h
  rw [basisMatrix, Matrix.smul_mul, h]
  ext i j
  by_cases h : i=j <;> simp [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply, h]

theorem inverse_mul_basis : basisInverse.map (Int.castRingHom ℚ) * basisMatrix = 1 :=
  mul_eq_one_comm.mp basis_mul_inverse

def basisUnit : GL Index ℚ := ⟨basisMatrix, basisInverse.map (Int.castRingHom ℚ),
  basis_mul_inverse, inverse_mul_basis⟩

def integerEmbedding : (Index → ℤ) →ₗ[ℤ] Space where
  toFun z i := z i
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

/-- The displayed integral basis, with rational quaternion coordinates. -/
def basisMap : (Index → ℤ) →ₗ[ℤ] Space :=
  (basisMatrix.mulVecLin.restrictScalars ℤ).comp integerEmbedding

/-- The glued Hurwitz lattice, defined by its explicit integral basis. -/
def lattice : Submodule ℤ Space := basisMap.range

theorem basisMap_apply (z : Index → ℤ) : basisMap z = basisMatrix *ᵥ integerEmbedding z := rfl

theorem integerEmbedding_mulVec (M : Matrix Index Index ℤ) (z : Index → ℤ) :
    integerEmbedding (M *ᵥ z) = M.map (Int.castRingHom ℚ) *ᵥ integerEmbedding z := by
  ext i
  simp [integerEmbedding, Matrix.mulVec, dotProduct]

theorem preserves_lattice_of_coordinates (M : RealMatrix) (N : Matrix Index Index ℤ)
    (h : M * basisMatrix = basisMatrix * N.map (Int.castRingHom ℚ)) :
    ∀ x ∈ lattice, M *ᵥ x ∈ lattice := by
  rintro x ⟨z,rfl⟩
  refine ⟨N *ᵥ z, ?_⟩
  rw [basisMap_apply, basisMap_apply, integerEmbedding_mulVec,
    Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec]

private theorem half_identity (M N : Matrix Index Index ℤ)
    (h : M * basisNumerator = 2 • (basisNumerator * N)) :
    ((1/2 : ℚ) • integerMatrix M) * basisMatrix =
      basisMatrix * integerMatrix N := by
  have hi := congrArg integerMatrix h
  simp only [map_mul, two_smul] at hi
  rw [basisMatrix]
  change ((1/2 : ℚ) • integerMatrix M) * ((1/2 : ℚ) • integerMatrix basisNumerator) =
    ((1/2 : ℚ) • integerMatrix basisNumerator) * integerMatrix N
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hi]
  simp only [map_add, map_mul, smul_add, ← add_smul]
  norm_num

theorem generatorA_basis : realification matrixA.conjTranspose * basisMatrix =
    basisMatrix * generatorACoordinates.map (Int.castRingHom ℚ) := by
  rw [numeratorA]
  exact half_identity _ _ integerA

theorem generatorB_basis : realification matrixBInv.conjTranspose * basisMatrix =
    basisMatrix * generatorBCoordinates.map (Int.castRingHom ℚ) := by
  rw [numeratorB]
  exact half_identity _ _ integerB

theorem generatorB_inverse_basis : realification matrixB.conjTranspose * basisMatrix =
    basisMatrix * generatorBInverseCoordinates.map (Int.castRingHom ℚ) := by
  rw [numeratorBInverse]
  exact half_identity _ _ integerBInverse

private theorem gram_of_row_identity (A : SixMatrix)
    (h : A * hermitianMatrix * A.conjTranspose = hermitianMatrix) :
    (realification A.conjTranspose).transpose * gramMatrix *
      realification A.conjTranspose = gramMatrix := by
  have hi := congrArg realification h
  simp only [map_mul, realification_conjTranspose] at hi
  simp only [realification_conjTranspose, Matrix.transpose_transpose,
    gramMatrix, Matrix.mul_smul, Matrix.smul_mul, hi]

theorem generatorA_gram : (realification matrixA.conjTranspose).transpose * gramMatrix *
    realification matrixA.conjTranspose = gramMatrix :=
  gram_of_row_identity _ matrixA_form

theorem generatorB_gram : (realification matrixBInv.conjTranspose).transpose * gramMatrix *
    realification matrixBInv.conjTranspose = gramMatrix :=
  gram_of_row_identity _ matrixBInv_form

theorem preserves_form_of_gram (M : RealMatrix) (h : M.transpose * gramMatrix * M = gramMatrix)
    (x y : Space) : form (M *ᵥ x) (M *ᵥ y) = form x y := by
  change dotProduct (M *ᵥ x) (gramMatrix *ᵥ (M *ᵥ y)) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  rfl

/-- Isometries of the actual integral lattice in these rational coordinates. -/
def latticeIsometries : Subgroup (GL Index ℚ) where
  carrier := {g | (∀ x y, form (g.val *ᵥ x) (g.val *ᵥ y) = form x y) ∧
    ∀ x, x ∈ lattice ↔ g.val *ᵥ x ∈ lattice}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg,hgL⟩ ⟨hh,hhL⟩
    constructor
    · intro x y
      change form ((g.val*h.val) *ᵥ x) ((g.val*h.val) *ᵥ y) = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
    · intro x
      change x ∈ lattice ↔ (g.val*h.val) *ᵥ x ∈ lattice
      rw [← Matrix.mulVec_mulVec]
      exact (hhL x).trans (hgL _)
  inv_mem' := by
    rintro g ⟨hg,hgL⟩
    constructor
    · intro x y
      change form (g.inv *ᵥ x) (g.inv *ᵥ y) = form x y
      have he := hg (g.inv *ᵥ x) (g.inv *ᵥ y)
      simpa only [Matrix.mulVec_mulVec, g.val_inv, Matrix.one_mulVec] using he.symm
    · intro x
      change x ∈ lattice ↔ g.inv *ᵥ x ∈ lattice
      have he := hgL (g.inv *ᵥ x)
      simpa only [Matrix.mulVec_mulVec, g.val_inv, Matrix.one_mulVec] using he.symm

private theorem mem_latticeIsometries (g : GL Index ℚ)
    (hf : g.val.transpose * gramMatrix * g.val = gramMatrix)
    (hi : ∀ x ∈ lattice, g.val *ᵥ x ∈ lattice)
    (hj : ∀ x ∈ lattice, g.inv *ᵥ x ∈ lattice) : g ∈ latticeIsometries := by
  refine ⟨preserves_form_of_gram _ hf, fun x => ⟨hi x, fun hx => ?_⟩⟩
  have h := hj _ hx
  simpa only [Matrix.mulVec_mulVec, g.inv_val, Matrix.one_mulVec] using h

theorem generatorA_isometry : rationalMatrices generatorA ∈ latticeIsometries := by
  apply mem_latticeIsometries
  · exact generatorA_gram
  · exact preserves_lattice_of_coordinates _ _ generatorA_basis
  · exact preserves_lattice_of_coordinates _ _ generatorA_basis

theorem generatorB_isometry : rationalMatrices generatorB ∈ latticeIsometries := by
  apply mem_latticeIsometries
  · exact generatorB_gram
  · exact preserves_lattice_of_coordinates _ _ generatorB_basis
  · exact preserves_lattice_of_coordinates _ _ generatorB_inverse_basis

/-- Generator arithmetic extends to the literal subgroup closure from MatrixData. -/
theorem rationalAction_isometry (g : matrixGroup) : rationalAction g ∈ latticeIsometries := by
  have h : matrixGroup ≤ latticeIsometries.comap rationalMatrices := by
    change Subgroup.closure {generatorA, generatorB} ≤ _
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact generatorA_isometry
    · exact generatorB_isometry
  exact h g.property

def integralAction : matrixGroup →* latticeIsometries :=
  rationalAction.codRestrict latticeIsometries rationalAction_isometry

theorem integralAction_injective : Function.Injective integralAction := by
  intro g h he
  apply rationalAction_injective
  exact congrArg Subtype.val he

/-- The concrete rational action preserves the integral lattice in both directions. -/
theorem linearAction_lattice (g : matrixGroup) (x : Space) :
    x ∈ lattice ↔ linearAction g x ∈ lattice := (rationalAction_isometry g).2 x

theorem linearAction_form (g : matrixGroup) (x y : Space) :
    form (linearAction g x) (linearAction g y) = form x y :=
  (rationalAction_isometry g).1 x y

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
