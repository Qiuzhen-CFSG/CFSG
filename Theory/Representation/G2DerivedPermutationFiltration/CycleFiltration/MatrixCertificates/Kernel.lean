module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Coordinates

/-!
# The half and quotient inside the numerical incidence kernel

This transports the certified half back along the saved cycle basis, into the
literal kernel of the 126-by-189 boundary matrix. Its actions are checked
against the saved flag permutations, and both factor matrices are computed
on the half and its literal quotient. The separate coset calculation identifies
this numerical boundary with the group's incidence boundary.
Source application: Aschbacher–Smith G.7.2(3), printed p.348/PDF p.359.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

set_option maxRecDepth 8192

def kernelProjection : cycleKernel →ₗ[ZMod 2] Half :=
  projection.comp cycleCoordinates.toLinearMap

def kernelHalf : Submodule (ZMod 2) cycleKernel := LinearMap.ker kernelProjection

def kernelHalfEquiv : kernelHalf ≃ₗ[ZMod 2] half where
  toFun v := ⟨cycleCoordinates v.val, v.property⟩
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp
  invFun v := ⟨cycleCoordinates.symm v.val, by
    change projection (cycleCoordinates (cycleCoordinates.symm v.val)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact v.property⟩
  left_inv v := by apply Subtype.ext; exact cycleCoordinates.symm_apply_apply v.val
  right_inv v := by apply Subtype.ext; exact cycleCoordinates.apply_symm_apply v.val

def kernelHalfCoordinates : kernelHalf ≃ₗ[ZMod 2] Half :=
  kernelHalfEquiv.trans halfCoordinates

noncomputable def kernelQuotientCoordinates : (cycleKernel ⧸ kernelHalf) ≃ₗ[ZMod 2] Half :=
  kernelProjection.quotKerEquivOfSurjective
    (projection_surjective.comp cycleCoordinates.surjective)

@[simp] theorem kernelQuotientCoordinates_mk (v : cycleKernel) :
    kernelQuotientCoordinates (Submodule.Quotient.mk v) = projection (cycleCoordinates v) := rfl

/-- The saved cycle action transported into the literal boundary kernel. -/
def kernelAction (a : Fin 2) : cycleKernel →ₗ[ZMod 2] cycleKernel :=
  cycleCoordinates.symm.conj (actionMatrix a).mulVecLin

@[simp] theorem cycleCoordinates_kernelAction (a : Fin 2) (v : cycleKernel) :
    cycleCoordinates (kernelAction a v) = (actionMatrix a).mulVec (cycleCoordinates v) := by
  simp only [kernelAction, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply]

/-- This is the literal saved flag permutation, rather than a stipulated factor action. -/
theorem kernelAction_flags (a : Fin 2) (v : cycleKernel) (i : Fin 189) :
    (kernelAction a v).val i = v.val (flagInverse a i) := by
  have hi : cycleEmbedding.mulVec (cycleCoordinates v) = v.val := by
    rw [← cycleCoordinates_symm_apply, LinearEquiv.symm_apply_apply]
  calc
    (kernelAction a v).val i = cycleEmbedding.mulVec (cycleCoordinates (kernelAction a v)) i := by
      rw [← cycleCoordinates_symm_apply, LinearEquiv.symm_apply_apply]
    _ = cycleEmbedding.mulVec ((actionMatrix a).mulVec (cycleCoordinates v)) i := by
      rw [cycleCoordinates_kernelAction]
    _ = v.val (flagInverse a i) := by
      rw [Matrix.mulVec_mulVec, embedding_action]
      exact congrFun hi (flagInverse a i)

theorem kernelAction_mem (a : Fin 2) {v : cycleKernel} (hv : v ∈ kernelHalf) :
    kernelAction a v ∈ kernelHalf := by
  change projection (cycleCoordinates (kernelAction a v)) = 0
  rw [cycleCoordinates_kernelAction, projection_action,
    show projection (cycleCoordinates v) = 0 from hv, Matrix.mulVec_zero]

def kernelHalfAction (a : Fin 2) : kernelHalf →ₗ[ZMod 2] kernelHalf :=
  (kernelAction a).restrict (fun _ hv => kernelAction_mem a hv)

def kernelQuotientAction (a : Fin 2) :
    (cycleKernel ⧸ kernelHalf) →ₗ[ZMod 2] (cycleKernel ⧸ kernelHalf) :=
  kernelHalf.mapQ (τ₁₂ := RingHom.id (ZMod 2)) kernelHalf (kernelAction a) (by
    intro v hv
    change kernelAction a v ∈ kernelHalf
    exact kernelAction_mem a (v := v) hv)

theorem kernelHalfCoordinates_action (a : Fin 2) (v : kernelHalf) :
    kernelHalfCoordinates (kernelHalfAction a v) =
      (factorMatrix 0 a).mulVec (kernelHalfCoordinates v) := by
  have h : kernelHalfEquiv (kernelHalfAction a v) = halfAction a (kernelHalfEquiv v) := by
    apply Subtype.ext
    change cycleCoordinates (kernelAction a v.val) = (actionMatrix a).mulVec (cycleCoordinates v.val)
    exact cycleCoordinates_kernelAction a v.val
  change halfCoordinates (kernelHalfEquiv (kernelHalfAction a v)) = _
  rw [h, halfCoordinates_action]
  rfl

theorem kernelQuotientCoordinates_action (a : Fin 2) (v : cycleKernel ⧸ kernelHalf) :
    kernelQuotientCoordinates (kernelQuotientAction a v) =
      (factorMatrix 1 a).mulVec (kernelQuotientCoordinates v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change kernelQuotientCoordinates (Submodule.Quotient.mk (kernelAction a v)) = _
    rw [kernelQuotientCoordinates_mk, kernelQuotientCoordinates_mk,
      cycleCoordinates_kernelAction, projection_action]

theorem kernelHalf_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (kernelHalfCoordinates.conj (kernelHalfAction a)) = factorMatrix 0 a := by
  have h : kernelHalfCoordinates.conj (kernelHalfAction a) = (factorMatrix 0 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change kernelHalfCoordinates (kernelHalfAction a (kernelHalfCoordinates.symm v)) = _
    rw [kernelHalfCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

theorem kernelQuotient_factorMatrix (a : Fin 2) :
    LinearMap.toMatrix' (kernelQuotientCoordinates.conj (kernelQuotientAction a)) = factorMatrix 1 a := by
  have h : kernelQuotientCoordinates.conj (kernelQuotientAction a) = (factorMatrix 1 a).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change kernelQuotientCoordinates (kernelQuotientAction a (kernelQuotientCoordinates.symm v)) = _
    rw [kernelQuotientCoordinates_action, LinearEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

theorem finrank_kernelHalf : Module.finrank (ZMod 2) kernelHalf = 32 := by
  rw [kernelHalfCoordinates.finrank_eq]
  simp [Half]

theorem finrank_kernelQuotient : Module.finrank (ZMod 2) (cycleKernel ⧸ kernelHalf) = 32 := by
  rw [kernelQuotientCoordinates.finrank_eq]
  simp [Half]

end G2DerivedPermutationFiltration.CycleData.Certificate
