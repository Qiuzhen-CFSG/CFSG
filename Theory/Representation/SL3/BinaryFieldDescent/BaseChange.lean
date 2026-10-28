module

public import Theory.Representation.ScalarDescent
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Scalar-extension comparisons for tensor products and duals

The standard tensor, dual and coefficient-extension isomorphisms intertwine
the group actions. For duals the scalar-extension isomorphism for linear-map
spaces supplies the pairing a·b·f(v), which is invariant under simultaneous
contragredient and original actions.

These are the functorial comparisons used in finite-field descent of the
SL₃ models, following GLS III, Remark 2.8.8. They require no classification
of representations and apply to arbitrary groups.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Representation

namespace Representation.BinaryFieldDescent
variable {F K G V W : Type*} [Field F] [Field K] [Algebra F K] [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Extend an actual intertwining equivalence. -/
def extendEquiv {ρ : Representation F G V} {τ : Representation F G W} (e : ρ.Equiv τ) :
    (extendScalars K ρ).Equiv (extendScalars K τ) :=
  .mk (LinearEquiv.baseChange F K V W e.toLinearEquiv) (by
    intro g
    change (e.toLinearMap.baseChange K).comp ((ρ g).baseChange K) =
      ((τ g).baseChange K).comp (e.toLinearMap.baseChange K)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, e.isIntertwining' g])

/-- Dualize an actual intertwining equivalence. -/
def dualEquiv {ρ : Representation F G V} {τ : Representation F G W} (e : ρ.Equiv τ) :
    ρ.dual.Equiv τ.dual :=
  .mk e.symm.toLinearEquiv.dualMap (by
    intro g
    ext f w
    exact congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w).symm)

/-- Scalar extension distributes over tensor products of representations. -/
def tensorBaseChange (ρ : Representation F G V) (τ : Representation F G W) :
    (extendScalars K (ρ.tprod τ)).Equiv
      ((extendScalars K ρ).tprod (extendScalars K τ)) :=
  .mk (TensorProduct.AlgebraTensorModule.distribBaseChange F K V W) (by
    intro g
    ext v w
    rfl)

/-- The canonical scalar-extension map on linear duals. -/
def dualBaseChangeLinearEquiv [FiniteDimensional F V] :
    (K ⊗[F] Module.Dual F V) ≃ₗ[K] Module.Dual K (K ⊗[F] V) :=
  (LinearMap.baseChangeLinearMapEquiv F K V F).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl K _) (TensorProduct.AlgebraTensorModule.rid F K K))

set_option maxRecDepth 2000 in
/-- Evaluation of an extended functional on a pure tensor. -/
theorem dualBaseChangeLinearEquiv_tmul [FiniteDimensional F V]
    (a b : K) (f : Module.Dual F V) (v : V) :
    dualBaseChangeLinearEquiv (a ⊗ₜ[F] f) (b ⊗ₜ[F] v) = a * b * algebraMap F K (f v) := by
  change (TensorProduct.AlgebraTensorModule.rid F K K)
    (LinearMap.baseChangeLinearMapEquiv F K V F (a ⊗ₜ[F] f) (b ⊗ₜ[F] v)) = _
  rw [LinearMap.baseChangeLinearMapEquiv_tmul, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, map_smul, TensorProduct.AlgebraTensorModule.rid_tmul]
  simp [Algebra.smul_def, mul_assoc, mul_comm]

set_option maxRecDepth 2000 in
/-- Scalar extension commutes with the genuine contragredient action. -/
def dualBaseChange [FiniteDimensional F V] (ρ : Representation F G V) :
    (extendScalars K ρ.dual).Equiv (extendScalars K ρ).dual :=
  .mk dualBaseChangeLinearEquiv (by
    intro g
    ext f v
    change dualBaseChangeLinearEquiv ((1 : K) ⊗ₜ[F] (ρ.dual g f)) ((1 : K) ⊗ₜ[F] v) =
      dualBaseChangeLinearEquiv ((1 : K) ⊗ₜ[F] f) ((1 : K) ⊗ₜ[F] (ρ g⁻¹ v))
    rw [dualBaseChangeLinearEquiv_tmul, dualBaseChangeLinearEquiv_tmul]
    rfl)


/-- Tensor two actual representation equivalences. -/
def tensorEquiv {U T : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup T] [Module F T]
    {ρ : Representation F G V} {τ : Representation F G W}
    {ρ' : Representation F G U} {τ' : Representation F G T}
    (e : ρ.Equiv τ) (f : ρ'.Equiv τ') :
    (ρ.tprod ρ').Equiv (τ.tprod τ') :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining'

/-- Restrict an actual equivalence to the binary field. -/
def restrictBinaryEquiv [Algebra (ZMod 2) F] [Module (ZMod 2) V] [Module (ZMod 2) W]
    {ρ : Representation F G V} {τ : Representation F G W} (e : ρ.Equiv τ) :
    (restrictScalars (k := ZMod 2) ρ).Equiv (restrictScalars (k := ZMod 2) τ) :=
  .mk (e.toLinearEquiv.restrictScalars (ZMod 2)) (by
    intro g
    ext v
    exact LinearMap.congr_fun (e.isIntertwining' g) v)

/-- Descend an actual Mathlib representation equivalence through an arbitrary
coefficient-field extension. -/
theorem equiv_of_extendScalars
    {F K G V W : Type*} [Field F] [Field K] [Algebra F K] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G V) (τ : Representation F G W)
    (h : Nonempty ((extendScalars K ρ).Equiv (extendScalars K τ))) :
    Nonempty (ρ.Equiv τ) := by
  obtain ⟨e⟩ := h
  obtain ⟨d⟩ := repEquiv_of_extendScalars ρ τ ⟨RepEquiv.ofRepresentationEquiv e⟩
  exact ⟨d.toRepresentationEquiv⟩

end Representation.BinaryFieldDescent
