module
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Commuting pointwise fixers under equivalences and central quotients

Automorphism transport sends the literal fixed component to its image and injects the commuting pointwise fixer. Perfectness makes the central-quotient action faithful. These bounds preserve both the actual quotient map and the component image.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {E Q : Type*} [Group E] [Group Q]

/-- Compatible fixed-subgroup transport with its ambient evaluation retained. -/
noncomputable def compatibleFixedSubgroupCongr (e : E ≃* Q) (a : MulAut E) :
    a.fixedSubgroup ≃* (MulAut.congr e a).fixedSubgroup :=
  fixedSubgroupEquivOfCompatible e a (MulAut.congr e a) (fun x => by
    change e (a x) = e (a (e.symm (e x)))
    rw [e.symm_apply_apply])

@[simp] theorem compatibleFixedSubgroupCongr_apply (e : E ≃* Q) (a : MulAut E)
    (x : a.fixedSubgroup) : (compatibleFixedSubgroupCongr e a x : Q) = e x := by
  unfold compatibleFixedSubgroupCongr
  exact fixedSubgroupEquivOfCompatible_apply _ _ _ _ _

/-- The subgroup of actors commuting with a and fixing its actual component pointwise. -/
@[expose] def commutingFixedComponentFixer (a : MulAut E) (B : Subgroup a.fixedSubgroup) :
    Subgroup (MulAut E) :=
  centralizer ({a} : Set (MulAut E)) ⊓
    fixingSubgroup (MulAut E) (B.map a.fixedSubgroup.subtype : Set E)

theorem commutingFixedComponentFixer_card_le_of_equiv
    [Finite E] [Finite Q] (a : MulAut E) (B : Subgroup a.fixedSubgroup) (e : E ≃* Q) :
    let b := MulAut.congr e a
    let C := B.map (compatibleFixedSubgroupCongr e a).toMonoidHom
    Nat.card (commutingFixedComponentFixer a B) ≤
      Nat.card (commutingFixedComponentFixer b C) := by
  let b := MulAut.congr e a
  let C := B.map (compatibleFixedSubgroupCongr e a).toMonoidHom
  let f : commutingFixedComponentFixer a B →* commutingFixedComponentFixer b C :=
    ((MulAut.congr e).toMonoidHom.comp (commutingFixedComponentFixer a B).subtype).codRestrict
      (commutingFixedComponentFixer b C) (fun u => by
        constructor
        · apply mem_centralizer_singleton_iff.mpr
          change MulAut.congr e (u : MulAut E) * MulAut.congr e a =
            MulAut.congr e a * MulAut.congr e (u : MulAut E)
          simpa only [map_mul] using congrArg (MulAut.congr e)
            (mem_centralizer_singleton_iff.mp u.property.1)
        · rintro ⟨x, hx⟩
          obtain ⟨y, hy, rfl⟩ := hx
          obtain ⟨w, hw, rfl⟩ := hy
          change (MulAut.congr e (u : MulAut E))
            ((compatibleFixedSubgroupCongr e a w : b.fixedSubgroup) : Q) =
            ((compatibleFixedSubgroupCongr e a w : b.fixedSubgroup) : Q)
          rw [compatibleFixedSubgroupCongr_apply]
          change e ((u : MulAut E) (e.symm (e (w : E)))) = e (w : E)
          rw [e.symm_apply_apply]
          exact congrArg e (u.property.2 ⟨(w : E), mem_map_of_mem a.fixedSubgroup.subtype hw⟩))
  have hi : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact (MulAut.congr e).injective (congrArg Subtype.val huv)
  exact Nat.card_le_card_of_injective f hi

theorem commutingFixedComponentFixer_card_le_quotient
    [Finite E] [Group.IsPerfect E] (a : MulAut E) (B : Subgroup a.fixedSubgroup)
    (e : (E ⧸ center E) ≃* Q) [Finite Q] :
    let b := centralQuotientAction e a
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
    let hc := fun x => (centralQuotientAction_apply e a x).symm
    let C := B.map (fixedSubgroupMap a b q hc)
    Nat.card (commutingFixedComponentFixer a B) ≤
      Nat.card (commutingFixedComponentFixer b C) := by
  let b := centralQuotientAction e a
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  let hc : ∀ x, q (a x) = b (q x) := fun x => (centralQuotientAction_apply e a x).symm
  let C := B.map (fixedSubgroupMap a b q hc)
  let f : commutingFixedComponentFixer a B →* commutingFixedComponentFixer b C :=
    ((centralQuotientAction e).comp (commutingFixedComponentFixer a B).subtype).codRestrict
      (commutingFixedComponentFixer b C) (fun u => by
        constructor
        · apply mem_centralizer_singleton_iff.mpr
          change centralQuotientAction e (u : MulAut E) * centralQuotientAction e a =
            centralQuotientAction e a * centralQuotientAction e (u : MulAut E)
          simpa only [map_mul] using congrArg (centralQuotientAction e)
            (mem_centralizer_singleton_iff.mp u.property.1)
        · rintro ⟨x, hx⟩
          obtain ⟨y, hy, rfl⟩ := hx
          obtain ⟨w, hw, rfl⟩ := hy
          change centralQuotientAction e (u : MulAut E)
            (e (QuotientGroup.mk' (center E) (w : E))) = e (QuotientGroup.mk' (center E) (w : E))
          rw [centralQuotientAction_apply]
          exact congrArg q (u.property.2 ⟨(w : E), mem_map_of_mem a.fixedSubgroup.subtype hw⟩))
  have hi : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact centralQuotientAction_injective e (congrArg Subtype.val huv)
  exact Nat.card_le_card_of_injective f hi
end MulAut
