module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.Reduction

/-!
# Linear extension of coordinate operators

An operator on each coordinate extends linearly to the whole vector space.
Adjoint equivariance of this extension can be checked on coordinate vectors,
or equivalently by one matrix identity for each column of the acting matrix.
This supplies the linear-algebra step in the adjoint realization of the
Cartan-plus-root lattice used by `F4IntegralChevalleyRepresentation`.

The construction is the finite-basis linear extension; the concrete operator
identities from Geck's integral construction are separate obligations.
-/

@[expose] public section

open scoped Matrix

namespace ReeF4.WordRelations.Faithfulness.Adjoint

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- Extend a family of coordinate operators linearly. -/
noncomputable def linearExtension (A : n → Matrix n n K) :
    (n → K) →ₗ[K] Matrix n n K where
  toFun v := ∑ j, v j • A j
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

/-- The extension has the specified value on each coordinate vector. -/
theorem linearExtension_single (A : n → Matrix n n K) (j : n) :
    linearExtension A (Pi.single j 1) = A j := by
  classical
  simp [linearExtension, Pi.single_apply, ite_smul]

/-- Adjoint equivariance of a linear map is determined by coordinate vectors. -/
theorem equivariant_iff_basis (D : (n → K) →ₗ[K] Matrix n n K)
    (g : (Matrix n n K)ˣ) :
    Equivariant D g ↔ ∀ j,
      D ((g : Matrix n n K) *ᵥ Pi.single j 1) * g = g * D (Pi.single j 1) := by
  constructor
  · intro h j
    exact h _
  · intro h v
    have hv : v = ∑ j, v j • Pi.single j 1 := by
      ext k
      simp [Pi.single_apply, smul_eq_mul]
    rw [hv]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun A => v j • A) (h j))

/-- Column-wise matrix identities suffice for the concrete coordinate extension. -/
theorem linearExtension_equivariant_iff (A : n → Matrix n n K)
    (g : (Matrix n n K)ˣ) :
    Equivariant (linearExtension A) g ↔
      ∀ j, (∑ i, (g : Matrix n n K) i j • A i) * g = g * A j := by
  rw [equivariant_iff_basis]
  simp only [linearExtension_single, Matrix.mulVec_single_one]
  rfl

end ReeF4.WordRelations.Faithfulness.Adjoint
