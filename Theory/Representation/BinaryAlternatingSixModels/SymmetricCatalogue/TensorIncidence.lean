module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.TensorIncidence.Cohomology
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Duality

/-!
# The binary S₆ tensor and the incidence building

The explicit endpoint-tensor map identifies top cohomology with the tensor of
the two marked natural modules, conditional only on irreducibility of its A₆
restriction. The product of the two invariant nondegenerate polar forms gives
an unconditional S₆-equivariant self-duality of the tensor. Dualizing the
cohomology comparison and using the actual graph's perfect incidence pairing
then identifies the tensor with top homology as well.

The final applications discharge both tensor/incidence premises in the
catalogue and invariant-line recognition reductions. Tensor irreducibility and
the two vertex quotient alternatives remain with their existing source owners;
no catalogue or recognition conclusion is assumed in either comparison.

Source: Aschbacher–Smith G.5.1–2, printed pp.342–343 (PDF pp.353–354).
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
open scoped TensorProduct
namespace BinaryAlternatingSix.SymmetricCatalogue

private noncomputable def naturalDualEquiv :
    NaturalModule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) NaturalModule :=
  polarForm.linearEquivOfInjective
    (LinearMap.ker_eq_bot.mp polarForm_nondegenerate.ker_eq_bot)
    (Subspace.dual_finrank_eq.symm)

private noncomputable def tensorSelfDualLinear :
    TensorModule ≃ₗ[ZMod 2] Module.Dual (ZMod 2) TensorModule :=
  (TensorProduct.congr naturalDualEquiv naturalDualEquiv).trans
    (TensorProduct.dualDistribEquiv (ZMod 2) NaturalModule NaturalModule)

@[simp] private theorem tensorSelfDualLinear_tmul (v w a b : NaturalModule) :
    tensorSelfDualLinear (v ⊗ₜ[ZMod 2] w) (a ⊗ₜ[ZMod 2] b) =
      polarForm v a * polarForm w b := by
  change TensorProduct.dualDistrib (ZMod 2) NaturalModule NaturalModule
    (TensorProduct.map polarForm polarForm (v ⊗ₜ[ZMod 2] w)) (a ⊗ₜ[ZMod 2] b) = _
  rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]

private theorem tensorSelfDualLinear_invariant (g : S6) (x y : TensorModule) :
    tensorSelfDualLinear (tensorAction g x) (tensorAction g y) =
      tensorSelfDualLinear x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul v w =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      change tensorSelfDualLinear
        (firstNatural g v ⊗ₜ[ZMod 2] secondNatural g w)
        (firstNatural g a ⊗ₜ[ZMod 2] secondNatural g b) = _
      simp only [tensorSelfDualLinear_tmul]
      exact congrArg₂ (· * ·) (polarAction_form g v a) (polarAction_form (diagramAut g) w b)

/-- The product of the natural polar forms is an invariant perfect tensor pairing. -/
noncomputable def tensorSelfDualEquiv : tensorAction.Equiv tensorAction.dual :=
  .mk tensorSelfDualLinear (fun g => by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change tensorSelfDualLinear (tensorAction g x) y =
      tensorSelfDualLinear x (tensorAction g⁻¹ y)
    have h := tensorSelfDualLinear_invariant g x (tensorAction g⁻¹ y)
    simpa only [Representation.self_inv_apply] using h)

@[simp] theorem tensorSelfDualEquiv_tmul (v w a b : NaturalModule) :
    tensorSelfDualEquiv (v ⊗ₜ[ZMod 2] w) (a ⊗ₜ[ZMod 2] b) =
      polarForm v a * polarForm w b := tensorSelfDualLinear_tmul v w a b

end BinaryAlternatingSix.SymmetricCatalogue

namespace BinaryAlternatingSix.SymmetricCatalogue

private noncomputable def dualCohomologyTensorEquiv
    (hTensor : IsIrreducible alternatingTensor) :
    tensorAction.dual.Equiv topCohomologyRepresentation.dual :=
  .mk (cohomologyTensorEquiv hTensor).toLinearEquiv.dualMap (fun g => by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (tensorAction g⁻¹ (cohomologyTensorEquiv hTensor v)) =
      f (cohomologyTensorEquiv hTensor (topCohomologyRepresentation g⁻¹ v))
    exact congrArg f (IntertwiningMap.isIntertwining _ _
      (cohomologyTensorEquiv hTensor).toIntertwiningMap g⁻¹ v).symm)

/-- The tensor identifies with the literal building cycle representation. -/
noncomputable def tensorHomologyEquiv (hTensor : IsIrreducible alternatingTensor) :
    tensorAction.Equiv topHomologyRepresentation :=
  (tensorSelfDualEquiv.trans (dualCohomologyTensorEquiv hTensor)).trans
    homologyCohomologyDualRepresentationEquiv.symm

/-- Catalogue assembly with the tensor/cohomology premise now discharged. -/
theorem classify_of_vertex_maps
    (hTensor : IsIrreducible alternatingTensor)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (hPoint : ∀ f : BinaryDuadModule.pointAction.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (hLine : ∀ f : lineRepresentation.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural)) : IsSymmetricModel ρ :=
  classify_of_incidence_maps hTensor (cohomologyTensorEquiv hTensor) ρ hPoint hLine

/-- The actual invariant-line consumer with both incidence comparisons discharged. -/
theorem homology_recognition_of_vertex_maps
    (hTensor : IsIrreducible alternatingTensor)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (hPoint : ∀ f : BinaryDuadModule.pointAction.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (hLine : ∀ f : lineRepresentation.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (h₁ : HasInvariantLine (ρ.comp A6.subtype) a6DuadStabilizer)
    (h₂ : HasInvariantLine (ρ.comp A6.subtype) a6SynthemeStabilizer) :
    Nonempty (ρ.Equiv topHomologyRepresentation) :=
  homology_recognition_of_incidence_maps hTensor (cohomologyTensorEquiv hTensor)
    (tensorHomologyEquiv hTensor) ρ hPoint hLine h₁ h₂

end BinaryAlternatingSix.SymmetricCatalogue

namespace BinaryAlternatingSix.SymmetricCatalogue

/-- The homology comparison respects the literal coordinate incidence pairing. -/
theorem tensorHomologyEquiv_pairing
    (hTensor : IsIrreducible alternatingTensor) (v : TensorModule) (w : FlagModule) :
    (∑ f : Flag, (tensorHomologyEquiv hTensor v).val f * w f) =
      tensorSelfDualEquiv v (cohomologyTensorEquiv hTensor (coboundaries.toSubmodule.mkQ w)) := by
  rw [← homologyCohomologyDualRepresentationEquiv_mk]
  change homologyCohomologyDualRepresentationEquiv
    (homologyCohomologyDualRepresentationEquiv.symm
      ((dualCohomologyTensorEquiv hTensor) (tensorSelfDualEquiv v)))
    (coboundaries.toSubmodule.mkQ w) = _
  rw [Representation.Equiv.apply_symm_apply]
  rfl

end BinaryAlternatingSix.SymmetricCatalogue
