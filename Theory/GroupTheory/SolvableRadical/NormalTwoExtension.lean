module

public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Solvable radicals in normal two-extensions

If a normal subgroup has a two-group radical and two-group quotient, the
ambient radical is a two-group and equals the ambient two-core. Restricting
the quotient map to the radical gives a two-group kernel: its inclusion in
the normal subgroup lands in that subgroup's radical. This proves the claim
without assuming that the extension is perfect.

A perfect group with simple two-core quotient has radical equal to its
core, providing the input for the affine SL₂ locals in PSL₃. The E2 consumer
is `InnerFamilies.TauMembers`.

Source: standard solvable extension theory; Aschbacher--Smith E.1.2(E2),
printed p.210, and the local extensions in F.1.12, printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The kernel and image of the restricted quotient map are two-groups. -/
theorem radical_isTwoGroup_of_normal_two_quotient (D : Subgroup G) [D.Normal]
    (hD : IsPGroup 2 (solvableRadical D)) (hq : IsPGroup 2 (G ⧸ D)) :
    IsPGroup 2 (solvableRadical G) := by
  let R := solvableRadical G
  let f := (QuotientGroup.mk' D).comp R.subtype
  let j : f.ker →* solvableRadical D :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩, by
        rw [← radical_subgroupOf_normal D]
        exact x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  have hk := hD.of_injective j hj
  exact ((hq.to_subgroup ⊤).comap_of_ker_isPGroup f hk).of_equiv
    ((MulEquiv.subgroupCongr (Subgroup.comap_top f)).trans topEquiv)

/-- The full radical, including all outer actors, is exactly the two-core. -/
theorem radical_eq_core_of_normal_two_quotient (D : Subgroup G) [D.Normal]
    (hD : IsPGroup 2 (solvableRadical D)) (hq : IsPGroup 2 (G ⧸ D)) :
    solvableRadical G = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, radical_isTwoGroup_of_normal_two_quotient D hD hq⟩
  · let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

/-- A perfect group with simple two-core quotient has no larger solvable radical. -/
theorem radical_eq_core_of_perfect_simple_core_quotient
    [Group.IsPerfect G] [IsSimpleGroup (G ⧸ pCore 2 G)] :
    solvableRadical G = pCore 2 G := by
  let Q := G ⧸ pCore 2 G
  let q : G →* Q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hR : solvableRadical Q = ⊥ := by
    rcases (inferInstance : (solvableRadical Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hs : Group.IsSolvable (⊤ : Subgroup Q) := h ▸ inferInstance
      let := hs
      exact (Group.IsPerfect.not_isSolvable Q
        (Group.isSolvable_of_surjective
          (f := (topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
          topEquiv.surjective)).elim
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    infer_instance
  rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _), hR]
  exact QuotientGroup.ker_mk' _

end Theory.GroupTheory
