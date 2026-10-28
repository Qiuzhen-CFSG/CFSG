module

public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Two-extensions of perfect groups with simple two-core quotient

If a perfect normal subgroup has nonabelian simple quotient by its two-core,
its radical is exactly that core. In an extension by a two-group the ambient
radical is again a two-group: its kernel and image in the quotient are both
two-groups. Thus the ambient radical equals the ambient two-core, even though
the whole extension need not be perfect. Its two-residual and solvable
residual both equal the original perfect normal subgroup.

Source: standard radical and residual calculus used in Aschbacher--Smith,
E.1.2(E2) and E.1.14(1), printed pp.210, 214.
-/

public section
open Subgroup
namespace Theory.GroupTheory.PerfectCoreTwoExtension
variable {G : Type*} [Group G] [Finite G]

/-- A perfect group with simple two-core quotient has no further radical. -/
theorem radical_eq_core [Group.IsPerfect G] [IsSimpleGroup (G ⧸ pCore 2 G)] :
    solvableRadical G = pCore 2 G := by
  have hr : solvableRadical (G ⧸ pCore 2 G) = ⊥ := by
    rcases (inferInstance : (solvableRadical (G ⧸ pCore 2 G)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hs : Group.IsSolvable (G ⧸ pCore 2 G) :=
        Group.isSolvable_of_surjective
          (f := (solvableRadical (G ⧸ pCore 2 G)).subtype)
          (by intro q; exact ⟨⟨q, h.symm ▸ mem_top q⟩, rfl⟩)
      exact (Group.IsPerfect.not_isSolvable _ hs).elim
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    infer_instance
  rw [← comap_solvableRadical_eq_of_solvable_ker (QuotientGroup.mk' (pCore 2 G))
    (QuotientGroup.mk'_surjective _), hr]
  exact QuotientGroup.ker_mk' _

/-- Two-group radical in the normal subgroup and two-group quotient imply
a two-group radical in the overgroup. -/
theorem radical_isTwoGroup (D : Subgroup G) [D.Normal]
    (hD : IsPGroup 2 (solvableRadical D)) (hq : IsPGroup 2 (G ⧸ D)) :
    IsPGroup 2 (solvableRadical G) := by
  let R := solvableRadical G
  let f := (QuotientGroup.mk' D).comp R.subtype
  let j : f.ker →* solvableRadical D :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        by rw [← radical_subgroupOf_normal D]; exact x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  have hk := hD.of_injective j hj
  exact ((hq.to_subgroup ⊤).comap_of_ker_isPGroup f hk).of_equiv
    ((MulEquiv.subgroupCongr (Subgroup.comap_top f)).trans topEquiv)

/-- The ambient radical is the two-core in every such two-extension. -/
theorem extension_radical_eq_core (D : Subgroup G) [D.Normal] [Group.IsPerfect D]
    [IsSimpleGroup (D ⧸ pCore 2 D)] (hq : IsPGroup 2 (G ⧸ D)) :
    solvableRadical G = pCore 2 G := by
  have hD : IsPGroup 2 (solvableRadical D) := by
    rw [radical_eq_core (G := D)]
    exact pCore_isPGroup
  have hR := radical_isTwoGroup D hD hq
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hR⟩
  · let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

/-- A perfect normal subgroup with two-group quotient is both residuals. -/
theorem residuals (D : Subgroup G) [D.Normal] [Group.IsPerfect D]
    (hq : IsPGroup 2 (G ⧸ D)) :
    pResidual 2 G = D ∧ solvableResidual G = D := by
  let : Group.IsNilpotent (G ⧸ D) := hq.isNilpotent
  have hs : solvableResidual G = D := le_antisymm
    (solvableResidual_le_of_solvable_quotient D) (le_solvableResidual_of_isPerfect D)
  refine ⟨le_antisymm (sInf_le ⟨inferInstance, hq⟩) ?_, hs⟩
  rw [← hs]
  apply le_sInf
  rintro N ⟨hn, hN⟩
  let := hn
  let : Group.IsNilpotent (G ⧸ N) := hN.isNilpotent
  exact solvableResidual_le_of_solvable_quotient N

end Theory.GroupTheory.PerfectCoreTwoExtension
