module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Form

/-!
# The natural complement calculation in a point/root frame

On the two selected tensor slices the actual invariant form is
`Tr(c det(u,v))`. If the actor contains the full upper root group, the root
with parameter c sends (0,c⁻¹) to its translate by (1,0), and that preimage
is perpendicular to (1,0). The zero coefficient is handled separately.

If the component intersection has only the upper-1 root, an outer actor
acts as an upper unipotent followed by Frobenius. Invariance then forces
`Tr(c)=0`, and (0,1) is the required perpendicular preimage. The sole finite
test has two field parameters, hence sixteen cases; no groups or bilinear
forms are enumerated.

The tensor preimages lie in the literal translated complement from the data.
The point/root frame and actor alternatives remain explicit prerequisites.
Source: Aschbacher–Smith, 14.4.10, first proof paragraph, printed p.1010.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
open Representation.SL2FourNatural

private theorem root_displacement (a : Field) (ha : a ≠ 0) :
    action (upper a) (![0, a⁻¹] : Vector) - ![0, a⁻¹] = e1 := by
  rw [upper_action]
  funext i
  fin_cases i <;> simp [e1, ha]

private theorem scalar_preimage_perpendicular (c : Field) (hc : c ≠ 0) :
    binaryPairing (c • e1) (![0, c⁻¹] : Vector) = 0 := by
  rw [binaryPairing_apply]
  have hw : wedge (c • e1) (![0, c⁻¹] : Vector) = 1 := by simp [wedge, e1, hc]
  rw [hw]
  decide +kernel

private theorem outer_preimage_perpendicular (c b : Field)
    (h : ∀ u v : Vector,
      binaryPairing (c • action (upper b) (frobeniusLinear u))
        (action (upper b) (frobeniusLinear v)) = binaryPairing (c • u) v) :
    binaryPairing (c • e1) e2 = 0 := by
  have he : ∀ c b : Field,
      binaryPairing (c • action (upper b) (frobeniusLinear e1))
        (action (upper b) (frobeniusLinear (![0, QuadraticAlgebra.omega] : Vector))) =
        binaryPairing (c • e1) (![0, QuadraticAlgebra.omega] : Vector) →
      binaryPairing (c • e1) e2 = 0 := by decide +kernel
  exact he c b (h e1 ![0, QuadraticAlgebra.omega])

variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V] {σ : Representation Bit D V}

/-- The natural finite calculation, with the two geometric prerequisites explicit. -/
theorem PointRootCoordinates.calculation (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) (hactor : ActorAlternatives p) :
    sourceTensorAction σ (cubicActor D) d.point ∈
      subspaceCommutator (sourceTensorAction σ)
        ((Submodule.span Bit {d.point}).orthogonalBilin d.form ⊓ d.secondSpace)
        (d.actor ⊓ (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) := by
  let rn := smallAction InvertedCubicTensor.cubic p.small
  obtain ⟨c, hc⟩ := p.form_scalar d p.small rn
  have hex : ∃ (a : Field) (w : Vector),
      componentActor hAD p.group (upper a) ∈ d.actor ∧
      action (upper a) w - w = e1 ∧ binaryPairing (c • e1) w = 0 := by
    rcases hactor with hall | ⟨a, b, _, hab⟩
    · by_cases hz : c = 0
      · refine ⟨1, ![0, (1 : Field)⁻¹], p.root_mem,
          root_displacement 1 one_ne_zero, ?_⟩
        simp [hz]
      · exact ⟨c, ![0, c⁻¹], hall c, root_displacement c hz,
          scalar_preimage_perpendicular c hz⟩
    · refine ⟨1, e2, p.root_mem, ?_, outer_preimage_perpendicular c b ?_⟩
      · simpa only [inv_one] using root_displacement 1 one_ne_zero
      · intro u v
        have he (q : Small) (w : Vector) :
            sourceTensorAction σ (1, a) (q ⊗ₜ[Bit] p.vector.symm w) =
              q ⊗ₜ[Bit] p.vector.symm (action (upper b) (frobeniusLinear w)) := by
          rw [tensor_tmul]
          change smallAction 1 q ⊗ₜ[Bit] σ a (p.vector.symm w) = _
          rw [map_one, Module.End.one_apply]
          apply congrArg (fun z : V => q ⊗ₜ[Bit] z)
          apply p.vector.injective
          rw [hab, p.vector.apply_symm_apply, p.vector.apply_symm_apply]
        have hi := d.form_invariant (1, a)
          (p.small ⊗ₜ[Bit] p.vector.symm u) (rn ⊗ₜ[Bit] p.vector.symm v)
        rwa [he, he, hc, hc] at hi
  obtain ⟨a, w, ha, hmove, hperp⟩ := hex
  let k := componentActor hAD p.group (upper a)
  have hdisplacement :
      sourceTensorAction σ k (rn ⊗ₜ[Bit] p.vector.symm w) - rn ⊗ₜ[Bit] p.vector.symm w =
        sourceTensorAction σ (cubicActor D) d.point := by
    rw [tensor_tmul, p.point_eq, tensor_tmul]
    change smallAction 1 rn ⊗ₜ[Bit] σ (componentActor hAD p.group (upper a)).2
      (p.vector.symm w) - rn ⊗ₜ[Bit] p.vector.symm w =
        rn ⊗ₜ[Bit] σ 1 (p.vector.symm e1)
    rw [map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      p.component_equivariant, ← tmul_sub, ← map_sub, hmove]
  apply Submodule.subset_span
  refine ⟨k, ⟨ha, componentActor_mem _ _⟩, rn ⊗ₜ[Bit] p.vector.symm w,
    ⟨?_, p.second_tmul_mem d _⟩, hdisplacement.symm⟩
  rw [LinearMap.orthogonal_span_singleton_eq_to_lin_ker]
  change d.form d.point (rn ⊗ₜ[Bit] p.vector.symm w) = 0
  rw [p.point_eq, hc]
  exact hperp

/-- Conditional assembly, retaining both outstanding geometric producers. -/
theorem calculation_of_normalization (hnatural : IsNaturalFour hAD σ)
    (hpoint : PointRootNormalization hAD σ) (hactor : ActorNormalization hAD σ) :
    ComplementIntersectionCalculation σ := by
  intro d
  obtain ⟨p⟩ := hpoint hnatural d
  exact p.calculation d (hactor d p)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
end
