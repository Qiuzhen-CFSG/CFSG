module
public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizer control across a whole-overlap amalgam

An amalgam isomorphism identifies membership in the opposite endpoint when
both middle groups are the whole intersections. Commutation with a middle
element transports through either endpoint. Consequently a centralizer
contained in one target endpoint forces the opposite source endpoint's
centralizer into the whole overlap.

This elementary transport is used in the common-centralizer step of
Aschbacher--Smith F.4.42, printed p.295. It does not identify centralizers
outside the source endpoints.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.RankTwoAmalgam.Iso
variable {G X : Type*} [Group G] [Group X]
  {P Q : Subgroup G} {P' B' Q' : Subgroup X}
  {h₀ : B' ≤ P'} {h₁ : B' ≤ Q'}

/-- An isomorphism of whole-overlap diagrams reflects membership in the other endpoint. -/
theorem right_mem_left_iff_of_overlap
    (F : Iso (ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (ofSubgroups P' B' Q' h₀ h₁))
    (hB : B' = P' ⊓ Q') (x : Q) :
    (F.right x).val ∈ P' ↔ x.val ∈ P := by
  constructor
  · intro hx
    let b : B' := ⟨(F.right x).val,hB.ge ⟨hx,(F.right x).property⟩⟩
    have he : inclusion h₁ b = F.right x := Subtype.ext rfl
    have hh := F.symm.right_commutes b
    change F.right.symm (inclusion h₁ b) = inclusion inf_le_right (F.middle.symm b) at hh
    rw [he,F.right.symm_apply_apply] at hh
    exact (congrArg Subtype.val hh).symm ▸ (F.middle.symm b).property.1
  · intro hx
    let b : (P ⊓ Q : Subgroup G) := ⟨x.val,hx,x.property⟩
    have he := congrArg Subtype.val (F.right_commutes b)
    exact he.symm ▸ h₀ (F.middle b).property

/-- A centralizer bound in one realization restricts the opposite endpoint centralizer in every realization of the same whole-overlap diagram. -/
theorem centralizer_right_le_left_of_overlap
    (F : Iso (ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (ofSubgroups P' B' Q' h₀ h₁))
    (hB : B' = P' ⊓ Q') (t : (P ⊓ Q : Subgroup G))
    (hc : Q' ⊓ centralizer ({(F.left (inclusion inf_le_left t)).val} : Set X) ≤ P') :
    Q ⊓ centralizer ({t.val} : Set G) ≤ P := by
  intro x hx
  let y : Q := ⟨x,hx.1⟩
  apply (F.right_mem_left_iff_of_overlap hB y).mp
  apply hc
  refine ⟨(F.right y).property,?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have he : (F.left (inclusion inf_le_left t)).val =
      (F.right (inclusion inf_le_right t)).val :=
    (congrArg Subtype.val (F.left_commutes t)).trans
      (congrArg Subtype.val (F.right_commutes t)).symm
  rw [he]
  have hh : y * inclusion inf_le_right t = inclusion inf_le_right t * y :=
    Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
  simpa only [map_mul, Subgroup.coe_mul] using
    congrArg (fun v : Q => (F.right v).val) hh

end Theory.GroupTheory.RankTwoAmalgam.Iso
