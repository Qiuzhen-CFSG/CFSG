module
public import Theory.Representation.BinaryOffender.Homogeneous.FaithfulOrbit

/-!
# Restricting the actual actor image to an invariant subspace

If an actor stabilizes I ≤ W, its faithful image on W surjects onto
its faithful image on I. An element fixing W fixes I, so the original
action maps factor through their literal kernels. The surjection
retains the image of each original actor element.

Source application: the seed action in Aschbacher–Smith, D.3.4(5), p.194.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem exists_restricted_image_surjection
    (A : Subgroup G) (I W : Submodule (ZMod 2) V)
    (hAI : A ≤ subspaceStabilizer ρ I) (hAW : A ≤ subspaceStabilizer ρ W)
    (hIW : I ≤ W) :
    ∃ f : restrictedSubgroup ρ W A →* restrictedSubgroup ρ I A, Function.Surjective f ∧
      ∀ a : A, f (restrictedActionSurjection ρ W A hAW a) =
        restrictedActionSurjection ρ I A hAI a := by
  let qW := restrictedActionSurjection ρ W A hAW
  let qI := restrictedActionSurjection ρ I A hAI
  have hqW : Function.Surjective qW := restrictedActionSurjection_surjective ρ W A hAW
  have hqI : Function.Surjective qI := restrictedActionSurjection_surjective ρ I A hAI
  have hk : qW.ker ≤ qI.ker := by
    intro a ha
    apply Subtype.ext
    apply subspaceImageRepresentation_injective ρ I
    ext v
    have hh := congrArg (fun b : restrictedSubgroup ρ W A =>
      subspaceImageRepresentation ρ W b.val ⟨v.val, hIW v.property⟩) ha
    change ρ a (v : V) = (v : V)
    exact congrArg (fun w : W => (w : V)) hh
  let f := qW.liftOfSurjective hqW ⟨qI, hk⟩
  have he (a : A) : f (qW a) = qI a :=
    qW.liftOfRightInverse_comp_apply _ _ _ a
  refine ⟨f, ?_, he⟩
  intro b
  obtain ⟨a, rfl⟩ := hqI b
  exact ⟨qW a, he a⟩
end Representation.BinaryOffender
