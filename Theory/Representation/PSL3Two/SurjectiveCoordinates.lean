module

public import Theory.Representation.PSL3Two.NaturalCoordinates

/-!
# Natural coordinates before eliminating the action kernel

A surjection onto SL₃(2), with compatible linear coordinates, already rules out
self-duality: an intertwiner would descend through the surjection and contradict
the explicit trace obstruction for the natural module. Once the original action
is faithful, the actor map is injective and gives the actual PSL₃(2) model.

This separates image recognition from kernel elimination in the constituent
argument of Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58,
printed p.1149.
-/

@[expose] public section
namespace BinaryLinearThree
open Representation
variable {A V : Type*} [_root_.Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Natural coordinates with a surjective actor map; its kernel is not assumed trivial. -/
structure NaturalCover (ρ : Representation (ZMod 2) A V) where
  actor : A →* Group
  surjective : Function.Surjective actor
  space : V ≃ₗ[ZMod 2] Vector
  intertwines : ∀ a v, space (ρ a v) = W (actor a) (space v)

/-- The natural-versus-dual obstruction survives a surjective change of actor. -/
theorem NaturalCover.not_self_dual {ρ : Representation (ZMod 2) A V}
    (m : NaturalCover ρ) : ¬ Nonempty (Representation.Equiv ρ ρ.dual) := by
  rintro ⟨e⟩
  apply AutomorphismAction.natural_not_equiv_dual
  have hs (a : A) (v : Vector) :
      m.space.symm (W (m.actor a) v) = ρ a (m.space.symm v) := by
    apply m.space.injective
    rw [m.space.apply_symm_apply, m.intertwines, m.space.apply_symm_apply]
  refine ⟨{ toLinearEquiv := m.space.symm.trans (e.toLinearEquiv.trans m.space.symm.dualMap)
            isIntertwining' := ?_ }⟩
  intro a
  obtain ⟨a, rfl⟩ := m.surjective a
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change e (m.space.symm (W (m.actor a) v)) (m.space.symm w) =
    e (m.space.symm v) (m.space.symm (W (m.actor a)⁻¹ w))
  rw [← map_inv, hs, hs]
  have he := LinearMap.congr_fun (e.isIntertwining' a) (m.space.symm v)
  simpa only [LinearMap.comp_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, Representation.Equiv.coe_toLinearMap] using
      congrArg (fun f : Module.Dual (ZMod 2) V => f (m.space.symm w)) he

/-- Faithfulness upgrades the surjective coordinates to an actual PSL₃(2) model. -/
noncomputable def NaturalCover.toNaturalModel {ρ : Representation (ZMod 2) A V}
    (m : NaturalCover ρ) (hf : Function.Injective ρ) : NaturalModel ρ := by
  have hi : Function.Injective m.actor := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro v
    apply m.space.injective
    rw [m.intertwines, m.intertwines, hab]
  let e : A ≃* Group := MulEquiv.ofBijective m.actor ⟨hi, m.surjective⟩
  refine ⟨e.trans Matrix.PSL3Two.equiv, m.space, ?_⟩
  intro a v
  change m.space (ρ a v) =
    W (Matrix.PSL3Two.equiv.symm (Matrix.PSL3Two.equiv (m.actor a))) (m.space v)
  rw [MulEquiv.symm_apply_apply]
  exact m.intertwines a v

end BinaryLinearThree

