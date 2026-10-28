module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Checks
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Coordinates on the cycle kernel, its half, and its literal quotient

The boundary splitting constructs an equivalence from its literal kernel to
64 coordinates. The adapted basis then gives a 32-dimensional half. Projection
onto the last 32 coordinates has exactly this half as kernel, so its first
isomorphism theorem gives coordinates on the literal quotient. The checked
block identities compute the restricted and quotient actions.

These are finite linear-algebra certificates for Aschbacher–Smith G.7.2(3),
printed p.348/PDF p.359. Identification with the actual coset representation
and invariance under the whole derived group are the assembly owner's work;
`Pair` supplies the ambient preserved/swapped pair for that argument.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

set_option maxRecDepth 8192

theorem first_eq_castAdd (i : Fin 32) : first i = Fin.castAdd 32 i := rfl

theorem last_eq_natAdd (i : Fin 32) : last i = Fin.natAdd 32 i := rfl

abbrev cycleKernel := LinearMap.ker boundaryMatrix.mulVecLin

def cycleCoordinates : cycleKernel ≃ₗ[ZMod 2] Space :=
  { extraction.mulVecLin.comp cycleKernel.subtype with
    invFun v := ⟨cycleEmbedding.mulVec v, by
      change boundaryMatrix.mulVec (cycleEmbedding.mulVec v) = 0
      rw [Matrix.mulVec_mulVec, boundary_embedding, Matrix.zero_mulVec]⟩
    left_inv v := by
      apply Subtype.ext
      change cycleEmbedding.mulVec (extraction.mulVec v.val) = v.val
      have hv : boundaryMatrix.mulVec v.val = 0 := v.property
      have h := congrArg (fun m : Matrix (Fin 189) (Fin 189) (ZMod 2) => m.mulVec v.val) boundary_splitting
      simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] using h
    right_inv v := by
      change extraction.mulVec (cycleEmbedding.mulVec v) = v
      rw [Matrix.mulVec_mulVec, extraction_embedding, Matrix.one_mulVec] }

theorem cycleCoordinates_apply (v : cycleKernel) :
    cycleCoordinates v = extraction.mulVec v.val := rfl

theorem cycleCoordinates_symm_apply (v : Space) :
    (cycleCoordinates.symm v).val = cycleEmbedding.mulVec v := rfl

def adaptedCoordinates : Space ≃ₗ[ZMod 2] Space :=
  { adaptedInverse.transpose.mulVecLin with
    invFun := adaptedBasis.transpose.mulVec
    left_inv v := by
      change adaptedBasis.transpose.mulVec (adaptedInverse.transpose.mulVec v) = v
      rw [Matrix.mulVec_mulVec, adapted_mul_inverse, Matrix.one_mulVec]
    right_inv v := by
      change adaptedInverse.transpose.mulVec (adaptedBasis.transpose.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_adapted, Matrix.one_mulVec] }

theorem adaptedCoordinates_symm_apply (v : Space) :
    adaptedCoordinates.symm v = adaptedBasis.transpose.mulVec v := rfl

theorem adaptedCoordinates_action (a : Fin 2) (v : Space) :
    adaptedCoordinates ((actionMatrix a).mulVec v) =
      (adaptedAction a).mulVec (adaptedCoordinates v) := by
  apply adaptedCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, adaptedCoordinates_symm_apply,
    Matrix.mulVec_mulVec, adapted_action, ← Matrix.mulVec_mulVec,
    ← adaptedCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

def projection : Space →ₗ[ZMod 2] Half where
  toFun v i := adaptedCoordinates v (last i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

/-- The saved half, as an actual subspace of the cycle-coordinate space. -/
def half : Submodule (ZMod 2) Space := LinearMap.ker projection

theorem mem_half (v : Space) : v ∈ half ↔ ∀ i, adaptedCoordinates v (last i) = 0 := by
  change projection v = 0 ↔ _
  exact funext_iff

/-- First coordinates of a member of the half. -/
def halfCoordinates : half ≃ₗ[ZMod 2] Half where
  toFun v i := adaptedCoordinates v.val (first i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp
  invFun v := ⟨adaptedCoordinates.symm (Fin.append v (0 : Half)), by
    rw [mem_half]
    intro i
    rw [LinearEquiv.apply_symm_apply, last_eq_natAdd, Fin.append_right]
    rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply adaptedCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    refine Fin.addCases (m := 32) (n := 32) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, first_eq_castAdd]
    · simpa only [Fin.append_right, Pi.zero_apply, last_eq_natAdd] using
        ((mem_half v.val).mp v.property j).symm
  right_inv v := by
    ext i
    change adaptedCoordinates (adaptedCoordinates.symm (Fin.append v (0 : Half))) (first i) = v i
    rw [LinearEquiv.apply_symm_apply, first_eq_castAdd, Fin.append_left]

theorem projection_surjective : Function.Surjective projection := by
  intro v
  refine ⟨adaptedCoordinates.symm (Fin.append (0 : Half) v), ?_⟩
  ext i
  change adaptedCoordinates (adaptedCoordinates.symm (Fin.append (0 : Half) v)) (last i) = v i
  rw [LinearEquiv.apply_symm_apply, last_eq_natAdd, Fin.append_right]

/-- Coordinates on the literal quotient by the saved half. -/
noncomputable def quotientCoordinates : (Space ⧸ half) ≃ₗ[ZMod 2] Half :=
  projection.quotKerEquivOfSurjective projection_surjective

@[simp] theorem quotientCoordinates_mk (v : Space) :
    quotientCoordinates (Submodule.Quotient.mk v) = projection v := by
  exact projection.quotKerEquivOfSurjective_apply_mk projection_surjective v

private theorem sum64 (f : Fin 64 → ZMod 2) :
    ∑ i, f i = (∑ i : Fin 32, f (first i)) + ∑ i : Fin 32, f (last i) :=
  by simpa only [first_eq_castAdd, last_eq_natAdd] using
    (Fin.sum_univ_add (a := 32) (b := 32) f)

theorem projection_action (a : Fin 2) (v : Space) :
    projection ((actionMatrix a).mulVec v) = (factorMatrix 1 a).mulVec (projection v) := by
  ext i
  change adaptedCoordinates ((actionMatrix a).mulVec v) (last i) = _
  rw [adaptedCoordinates_action]
  change (∑ j, adaptedAction a (last i) j * adaptedCoordinates v j) = _
  rw [sum64]
  simp only [adapted_lower_left, zero_mul, Finset.sum_const_zero, zero_add,
    adapted_bottom_block]
  rfl

theorem action_mem_half (a : Fin 2) {v : Space} (hv : v ∈ half) :
    (actionMatrix a).mulVec v ∈ half := by
  change projection ((actionMatrix a).mulVec v) = 0
  rw [projection_action, show projection v = 0 from hv, Matrix.mulVec_zero]

/-- Restriction of the saved actor to the actual half. -/
def halfAction (a : Fin 2) : half →ₗ[ZMod 2] half :=
  (actionMatrix a).mulVecLin.restrict (fun _ hv => action_mem_half a hv)

/-- The induced map on the literal quotient. -/
def quotientAction (a : Fin 2) : (Space ⧸ half) →ₗ[ZMod 2] (Space ⧸ half) :=
  half.mapQ (τ₁₂ := RingHom.id (ZMod 2)) half (actionMatrix a).mulVecLin (by
    intro v hv
    change (actionMatrix a).mulVec v ∈ half
    exact action_mem_half a (v := v) hv)

theorem halfCoordinates_action (a : Fin 2) (v : half) :
    halfCoordinates (halfAction a v) = (factorMatrix 0 a).mulVec (halfCoordinates v) := by
  ext i
  change adaptedCoordinates ((actionMatrix a).mulVec v.val) (first i) = _
  rw [adaptedCoordinates_action]
  change (∑ j, adaptedAction a (first i) j * adaptedCoordinates v.val j) = _
  rw [sum64]
  simp only [((mem_half v.val).mp v.property), mul_zero, Finset.sum_const_zero,
    add_zero, adapted_top_block]
  rfl

theorem quotientCoordinates_action (a : Fin 2) (v : Space ⧸ half) :
    quotientCoordinates (quotientAction a v) =
      (factorMatrix 1 a).mulVec (quotientCoordinates v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change quotientCoordinates (Submodule.Quotient.mk ((actionMatrix a).mulVec v)) = _
    rw [quotientCoordinates_mk, quotientCoordinates_mk, projection_action]

/-- Both actors have the published first factor matrix on the saved half. -/
theorem half_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (halfCoordinates.conj (halfAction a)) = factorMatrix 0 a := by
  have h : halfCoordinates.conj (halfAction a) = (factorMatrix 0 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change halfCoordinates (halfAction a (halfCoordinates.symm v)) = _
    rw [halfCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

/-- Both actors have the published second factor matrix on the literal quotient. -/
theorem quotient_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (quotientCoordinates.conj (quotientAction a)) = factorMatrix 1 a := by
  have h : quotientCoordinates.conj (quotientAction a) = (factorMatrix 1 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change quotientCoordinates (quotientAction a (quotientCoordinates.symm v)) = _
    rw [quotientCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

theorem finrank_cycleKernel : Module.finrank (ZMod 2) cycleKernel = 64 := by
  rw [cycleCoordinates.finrank_eq]
  simp [Space]

theorem finrank_half : Module.finrank (ZMod 2) half = 32 := by
  rw [halfCoordinates.finrank_eq]
  simp [Half]

theorem finrank_quotient : Module.finrank (ZMod 2) (Space ⧸ half) = 32 := by
  rw [quotientCoordinates.finrank_eq]
  simp [Half]

end G2DerivedPermutationFiltration.CycleData.Certificate
