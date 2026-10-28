module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Coordinates

/-!
# The deleted-module calculation in normalized coordinates

Two successive Klein-four displacements produce the cubic translate of the
point. The first displacement lies in its perpendicular by invariance of the
supplied form and point fixation. Thus identifying that form with a coordinate
pairing is unnecessary. The natural-factor displacement preimage puts every
required tensor in the literal first range and its specified cubic translate.

This proves the finite calculation from the explicit `Placement` geometry.
Construction of that geometry remains necessary for the unconditional source
branch. The bilinear form, spaces and actors throughout are those of the
actual `ComplementIntersectionData`.

Source: Aschbacher–Smith, 14.4.10, printed p.1010, using the invariant form
of 12.8.8(2), printed p.851.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
namespace Deleted
variable {σ : Representation (ZMod 2) D V}

theorem tensor_tmul (a : Three × D) (n : Natural) (v : V) :
    sourceTensorAction σ a (n ⊗ₜ[ZMod 2] v) =
      naturalAction a.1 n ⊗ₜ[ZMod 2] σ a.2 v := rfl

theorem Placement.first_tmul_mem (f : V ≃ₗ[ZMod 2] Core)
    (d : ComplementIntersectionData σ) (p : Placement (hAD := hAD) f d) (v : V) :
    p.natural ⊗ₜ[ZMod 2] v ∈ d.firstSpace := by
  rw [d.first_eq_range]
  refine ⟨p.preimage ⊗ₜ[ZMod 2] v, ?_⟩
  change sourceTensorAction σ d.element (p.preimage ⊗ₜ[ZMod 2] v) -
    p.preimage ⊗ₜ[ZMod 2] v = _
  rw [tensor_tmul, element_second_eq_one hAD d, map_one, Module.End.one_apply,
    ← sub_tmul, p.displacement]

theorem Placement.second_tmul_mem (f : V ≃ₗ[ZMod 2] Core)
    (d : ComplementIntersectionData σ) (p : Placement (hAD := hAD) f d) (v : V) :
    naturalAction InvertedCubicTensor.cubic p.natural ⊗ₜ[ZMod 2] v ∈ d.secondSpace := by
  rw [d.second_eq_translate]
  refine Submodule.mem_map.mpr ⟨_, p.first_tmul_mem f d v, ?_⟩
  rw [tensor_tmul]
  change naturalAction InvertedCubicTensor.cubic p.natural ⊗ₜ[ZMod 2] σ 1 v = _
  rw [map_one, Module.End.one_apply]

theorem conjugate_displacement
    (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (g : Five) (a : AltFive) (u w : Core)
    (huw : permAction a.val u - u = w) :
    σ (inclusion hAD (conjugate g a)) (f.symm (permAction g u)) -
      f.symm (permAction g u) = f.symm (permAction g w) := by
  apply f.injective
  rw [map_sub, hf]
  simp only [f.apply_symm_apply]
  change permAction (g * a.val * g⁻¹) (permAction g u) - permAction g u = _
  rw [← Module.End.mul_apply, ← map_mul]
  have he : (g * a.val * g⁻¹) * g = g * a.val := by group
  rw [he, map_mul, Module.End.mul_apply, ← map_sub, huw]

/-- Invariance makes a displacement orthogonal to every fixed point. -/
theorem displacement_orthogonal (d : ComplementIntersectionData σ)
    (a : Three × D) (ha : a ∈ d.actor) (y : IntersectionSpace V) :
    sourceTensorAction σ a y - y ∈
      (Submodule.span (ZMod 2) {d.point}).orthogonalBilin d.form := by
  rw [LinearMap.orthogonal_span_singleton_eq_to_lin_ker, LinearMap.mem_ker, map_sub]
  apply sub_eq_zero.mpr
  have h := d.form_invariant a d.point y
  rwa [d.point_fixed a (d.actor_le_sylow ha)] at h

theorem Placement.calculation
    (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (d : ComplementIntersectionData σ) (p : Placement (hAD := hAD) f d) :
    sourceTensorAction σ (cubicActor D) d.point ∈
      subspaceCommutator (sourceTensorAction σ)
        ((Submodule.span (ZMod 2) {d.point}).orthogonalBilin d.form ⊓ d.secondSpace)
        (d.actor ⊓ (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) := by
  let rn := naturalAction InvertedCubicTensor.cubic p.natural
  let q := f.symm (permAction p.coordinate middle)
  let u := f.symm (permAction p.coordinate seed)
  let a := componentActor hAD (conjugate p.coordinate first)
  let b := componentActor hAD (conjugate p.coordinate second)
  have hfirst : sourceTensorAction σ a (rn ⊗ₜ[ZMod 2] u) - rn ⊗ₜ[ZMod 2] u =
      rn ⊗ₜ[ZMod 2] q := by
    rw [tensor_tmul]
    change naturalAction 1 rn ⊗ₜ[ZMod 2]
      σ (inclusion hAD (conjugate p.coordinate first)) u - rn ⊗ₜ[ZMod 2] u = _
    rw [map_one, Module.End.one_apply, ← tmul_sub]
    exact congrArg (fun v => rn ⊗ₜ[ZMod 2] v)
      (conjugate_displacement f hf p.coordinate first seed middle first_displacement)
  have hsecond : sourceTensorAction σ b (rn ⊗ₜ[ZMod 2] q) - rn ⊗ₜ[ZMod 2] q =
      sourceTensorAction σ (cubicActor D) d.point := by
    rw [tensor_tmul, p.point_eq, tensor_tmul]
    change naturalAction 1 rn ⊗ₜ[ZMod 2]
      σ (inclusion hAD (conjugate p.coordinate second)) q - rn ⊗ₜ[ZMod 2] q =
        rn ⊗ₜ[ZMod 2] σ 1 (f.symm (permAction p.coordinate point))
    rw [map_one, Module.End.one_apply, map_one, Module.End.one_apply, ← tmul_sub]
    exact congrArg (fun v => rn ⊗ₜ[ZMod 2] v)
      (conjugate_displacement f hf p.coordinate second middle point second_displacement)
  apply Submodule.subset_span
  refine ⟨b, ⟨p.second_mem, componentActor_mem _⟩, rn ⊗ₜ[ZMod 2] q, ⟨?_, ?_⟩,
    hsecond.symm⟩
  · rw [← hfirst]
    exact displacement_orthogonal d a p.first_mem _
  · exact p.second_tmul_mem f d q

theorem calculation_of_actorPlacement
    (hdeleted : IsDeletedFour hAD σ) (hplacement : ActorPlacement hAD σ) :
    ComplementIntersectionCalculation σ := by
  obtain ⟨f, hf⟩ := hdeleted
  have he := deleted_extension_equivariant σ f hf
  intro d
  obtain ⟨p⟩ := hplacement f he d
  exact p.calculation f he d

end Deleted
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
