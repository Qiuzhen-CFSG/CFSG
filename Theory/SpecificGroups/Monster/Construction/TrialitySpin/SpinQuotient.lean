module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinAction
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Extraspecial

/-!
# The faithful extraspecial spin action

The concrete kernel `⟨k1⟩` allows the `Q1` spin action to descend to the
actual quotient `Q1/⟨k1⟩`. Transport through its canonical isomorphism with
the image of `Q1` in `N/K` gives a faithful action of that fixed extraspecial
group. The specified central involution acts as minus identity, and the
normalized positive form is invariant. These are the group and action inputs
to the real irreducibility theorem; irreducibility is not assumed here.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6 and the application following
Lemma 27.5, printed pp. 62–63 and 147.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin.SpinAction

/-- The faithful real action of the actual extraspecial quotient. -/
def quotientRepresentation : Representation ℝ Q1Quotient SpinSpace :=
  QuotientGroup.lift (K1.subgroupOf Q1) q1Representation q1Representation_kernel.ge

theorem quotientRepresentation_mk (q : Q1) :
    quotientRepresentation (QuotientGroup.mk' (K1.subgroupOf Q1) q) =
      q1Representation q := rfl

theorem quotientRepresentation_faithful : Function.Injective quotientRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr q1Representation_kernel.symm

/-- Identify the action on `Q1/⟨k1⟩` with an action on its concrete image in `N/K`. -/
def imageRepresentation : Representation ℝ Q1Image SpinSpace :=
  quotientRepresentation.comp q1QuotientEquivImage.symm.toMonoidHom

theorem imageRepresentation_faithful : Function.Injective imageRepresentation :=
  quotientRepresentation_faithful.comp q1QuotientEquivImage.symm.injective

theorem quotientEquivImage_mk (q : Q1) :
    q1QuotientEquivImage (QuotientGroup.mk' (K1.subgroupOf Q1) q) = q1ImageMap q := rfl

theorem imageRepresentation_map (q : Q1) :
    imageRepresentation (q1ImageMap q) = q1Representation q := by
  change quotientRepresentation (q1QuotientEquivImage.symm (q1ImageMap q)) = _
  rw [← quotientEquivImage_mk, q1QuotientEquivImage.symm_apply_apply]
  rfl

theorem imageRepresentation_center :
    imageRepresentation q1ImageCenterGenerator = -1 := by
  have he : q1ImageCenterGenerator = q1ImageMap ⟨z1N,z1N_mem_Q1⟩ := rfl
  rw [he, imageRepresentation_map]
  exact representation_z_eq

theorem imageRepresentation_isometry (q : Q1Image) (v w : SpinSpace) :
    bothAxesDomain.form (imageRepresentation q v) (imageRepresentation q w) =
      bothAxesDomain.form v w := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective q
  rw [imageRepresentation_map]
  exact representation_isometry (q1Inclusion q) v w

end Sporadic.Monster.Construction.TrialitySpin.SpinAction
