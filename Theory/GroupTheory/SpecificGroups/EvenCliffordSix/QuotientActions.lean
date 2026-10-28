module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Structure
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SignedAction

/-!
# The signed action on the two intrinsic quotient layers

The coordinate model is the marked central product `C₄ * Q₈ * Q₈`. Its
Frattini subgroup is the common sign involution and its full center is the
cyclic-four volume subgroup. Fixation of volume therefore fixes the full
center. The first-isomorphism identifications intertwine the canonical
quotient actions with the literal binary permutation representations: the
augmentation core modulo Frattini and the natural deleted section modulo
the full center. Each equation also retains an arbitrary automorphism of
the alternating actor, for a consumer's original six-point marking.

The proofs use quotient representatives and the established coordinate-map
equations, joining the independently proved factor structure and signed action.
No ambient covering group or transported action enters the construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6),
printed pp.410 and 412 (PDF pp.421 and 423). These are the intrinsic model
facts for the quartic radical; its recognition inside a cover remains separate.
-/

@[expose] public section

namespace EvenCliffordSix
open BinaryPermutation

/-- The coordinate sign kernel inherits characteristicity from its proved
Frattini identification. -/
instance signKernel_characteristic : signKernel.Characteristic := by
  rw [← frattini_eq_signKernel]
  infer_instance

/-- The intrinsic alternating action fixes the entire cyclic-four center. -/
theorem action_center (a : A) (x : Model) (hx : x ∈ Subgroup.center Model) :
    action a x = x := by
  rw [Structure.center_eq_zpowers_volume] at hx
  obtain ⟨n, rfl⟩ := hx
  rw [map_zpow, action_volume]

/-- The action induced on the literal sign quotient is the even permutation
representation under the original coordinate projection. -/
theorem quotientEquiv_action (a : A) (v : Model ⧸ signKernel) :
    quotientEquiv (Subgroup.quotientAut signKernel (action a) v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val (quotientEquiv v).toAdd) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective signKernel v
  rw [Subgroup.quotientAut_apply_mk, quotientEquiv_mk, quotientEquiv_mk]
  exact action_projection a x

/-- The same coordinate equation on the actual Frattini quotient. -/
theorem frattiniQuotientEquiv_action (a : A) (v : Model ⧸ frattini Model) :
    frattiniQuotientEquiv (Subgroup.quotientAut (frattini Model) (action a) v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val
        (frattiniQuotientEquiv v).toAdd) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Model) v
  rw [Subgroup.quotientAut_apply_mk, frattiniQuotientEquiv_mk, frattiniQuotientEquiv_mk]
  exact action_projection a x

/-- The action induced on the full-center quotient is the natural deleted
permutation representation under the original natural projection. -/
theorem centerQuotientEquiv_action (a : A) (v : Model ⧸ Subgroup.center Model) :
    (Structure.centerQuotientEquiv
      (Subgroup.quotientAut (Subgroup.center Model) (action a) v)).toAdd =
      naturalRepresentation (Fin 6) a.val (Structure.centerQuotientEquiv v).toAdd := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Model) v
  rw [Subgroup.quotientAut_apply_mk, Structure.centerQuotientEquiv_mk,
    Structure.centerQuotientEquiv_mk]
  exact action_naturalProjection a x

/-- Changing the six-point actor marking still fixes the full center. -/
theorem precomposedAction_center (e : MulAut A) (a : A) (x : Model)
    (hx : x ∈ Subgroup.center Model) : precomposedAction e a x = x :=
  action_center (e a) x hx

/-- The sign-quotient equation retains the actor automorphism explicitly. -/
theorem quotientEquiv_precomposedAction (e : MulAut A) (a : A)
    (v : Model ⧸ signKernel) :
    quotientEquiv (Subgroup.quotientAut signKernel (precomposedAction e a) v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) (e a).val (quotientEquiv v).toAdd) :=
  quotientEquiv_action (e a) v

/-- The Frattini-quotient equation retains the actor automorphism explicitly. -/
theorem frattiniQuotientEquiv_precomposedAction (e : MulAut A) (a : A)
    (v : Model ⧸ frattini Model) :
    frattiniQuotientEquiv
      (Subgroup.quotientAut (frattini Model) (precomposedAction e a) v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) (e a).val
        (frattiniQuotientEquiv v).toAdd) :=
  frattiniQuotientEquiv_action (e a) v

/-- The full-center quotient equation retains the actor automorphism explicitly. -/
theorem centerQuotientEquiv_precomposedAction (e : MulAut A) (a : A)
    (v : Model ⧸ Subgroup.center Model) :
    (Structure.centerQuotientEquiv
      (Subgroup.quotientAut (Subgroup.center Model) (precomposedAction e a) v)).toAdd =
      naturalRepresentation (Fin 6) (e a).val (Structure.centerQuotientEquiv v).toAdd :=
  centerQuotientEquiv_action (e a) v

end EvenCliffordSix
