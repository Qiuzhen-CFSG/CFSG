module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.IntrinsicCoordinates
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ReflectionReduction
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.PlaneNormality

/-!
# Intrinsic hyperbolic recognition with the original reflection actions

The two involution frames give all sixty-four normal words. The genuine
fixed quotient planes of the two original reflections force one of the two
UT₃(F₄) word laws. Their unique shear formulas preserve each of the two
root planes separately. Thus both the group equivalence and its two
normal elementary sixteen-groups retain the original carrier and actors.
Source: Aschbacher, *Sporadic Groups* (1994), 45.3, printed pp.242–243.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix.PSL3Four
namespace Theory.GroupTheory.HyperbolicRecognition
variable {K : Type*} [Group K]

/-- A literal root realization retaining the two original automorphisms. -/
structure ActorRootRealization (a b : MulAut K) where
  equiv : K ≃* RootNormalizerModel.Root
  first_left : (transportedPlane₁ equiv).map a.toMonoidHom = transportedPlane₁ equiv
  first_right : (transportedPlane₂ equiv).map a.toMonoidHom = transportedPlane₂ equiv
  second_left : (transportedPlane₁ equiv).map b.toMonoidHom = transportedPlane₁ equiv
  second_right : (transportedPlane₂ equiv).map b.toMonoidHom = transportedPlane₂ equiv

private theorem realize_twoCases (M : Cross) (C : K ≃* Word M)
    (a b : MulAut K) (S T : Frame) (hS : FirstReflection M S)
    (hT : SecondReflection M T)
    (ha : ∀ x, (C (a x)).vector = reflectA S (C x).vector)
    (hb : ∀ x, (C (b x)).vector = reflectB T (C x).vector)
    (hM : TwoCases M) : Nonempty (ActorRootRealization a b) := by
  rcases hM with rfl | rfl
  · obtain rfl := aligned_first_frame S hS
    obtain rfl := aligned_second_frame T hT
    have h₁ := reflectionA_preserves_planes 0 C a ha
    have h₂ := reflectionB_preserves_planes 0 C b hb
    exact ⟨⟨C.trans (modelEquiv 0),h₁.1,h₁.2,h₂.1,h₂.2⟩⟩
  · obtain rfl := crossed_first_frame S hS
    obtain rfl := crossed_second_frame T hT
    have h₁ := reflectionA_preserves_planes 1 C a ha
    have h₂ := reflectionB_preserves_planes 1 C b hb
    exact ⟨⟨C.trans (modelEquiv 1),h₁.1,h₁.2,h₂.1,h₂.2⟩⟩

/-- The actual hyperbolic factors and genuine source reflections recognize
UT₃(F₄), retaining both original actions on its two elementary sixteen-groups. -/
theorem nonempty_actorRootRealization (F : HyperbolicFactors K)
    (P : HyperbolicFrame F.A F.z) (Q : HyperbolicFrame F.B F.u)
    (a : F.FirstActor) (b : F.SecondActor) : Nonempty (ActorRootRealization a.aut b.aut) := by
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [F.card]; decide)
  obtain ⟨C⟩ := nonempty_markedCoordinates F P Q
  obtain ⟨S,hS,ha⟩ := C.first_reflection a
  obtain ⟨T,hT,hb⟩ := C.second_reflection b
  exact realize_twoCases C.matrix C.equiv a.aut b.aut S T hS hT ha hb (C.twoCases a b)

/-- The intrinsic source group is the literal root group UT₃(F₄). -/
theorem nonempty_rootEquiv (F : HyperbolicFactors K)
    (P : HyperbolicFrame F.A F.z) (Q : HyperbolicFrame F.B F.u)
    (a : F.FirstActor) (b : F.SecondActor) : Nonempty (K ≃* RootNormalizerModel.Root) := by
  obtain ⟨e⟩ := nonempty_actorRootRealization F P Q a b
  exact ⟨e.equiv⟩

/-- The exact two elementary sixteen-groups on the original carrier, with
both original source reflections preserving each subgroup individually. -/
theorem exists_two_elementary_planes (F : HyperbolicFactors K)
    (P : HyperbolicFrame F.A F.z) (Q : HyperbolicFrame F.B F.u)
    (a : F.FirstActor) (b : F.SecondActor) :
    ∃ E₁ E₂ : Subgroup K,
      IsElementaryAbelian 2 E₁ ∧ IsElementaryAbelian 2 E₂ ∧
      Nat.card E₁ = 16 ∧ Nat.card E₂ = 16 ∧ E₁ ≠ E₂ ∧
      E₁ ⊓ E₂ = center K ∧
      (∀ E : Subgroup K, (IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔ E = E₁ ∨ E = E₂) ∧
      E₁.map a.aut.toMonoidHom = E₁ ∧ E₂.map a.aut.toMonoidHom = E₂ ∧
      E₁.map b.aut.toMonoidHom = E₁ ∧ E₂.map b.aut.toMonoidHom = E₂ := by
  obtain ⟨e⟩ := nonempty_actorRootRealization F P Q a b
  exact ⟨transportedPlane₁ e.equiv,transportedPlane₂ e.equiv,inferInstance,inferInstance,
    card_transportedPlane₁ e.equiv,card_transportedPlane₂ e.equiv,
    transportedPlanes_ne e.equiv,transportedPlanes_inf e.equiv,
    transported_elementary_sixteen_iff e.equiv,e.first_left,e.first_right,
    e.second_left,e.second_right⟩

end Theory.GroupTheory.HyperbolicRecognition
