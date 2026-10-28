module

public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Components in the fixed subgroup of a central quotient

When the two-residual of the quotient fixed subgroup is quasisimple, it is
perfect and equals its solvable residual. Lift the latter to a perfect
pointwise-fixed subgroup upstairs. Reflection of perfect-subgroup containment
and component maximality identify this lift with the given component.
Thus its quotient image is exactly O² of the full quotient fixed subgroup.
This avoids assuming that all fixed quotient elements lift to fixed elements.

Source: Aschbacher–Smith, the central-cover step in 16.3.11(3), p.1181.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {K : Type*} [Group K] [Finite K]

/-- The two-residual of the actual fixed subgroup, embedded in the group. -/
abbrev fixedTwoResidual (a : MulAut K) : Subgroup K :=
  (pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype

omit [Finite K] in
/-- Fixed elements normalize the embedded two-residual. -/
theorem fixed_le_normalizer_fixedTwoResidual (a : MulAut K) : a.fixedSubgroup ≤ normalizer (fixedTwoResidual a : Set K) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  let f := a.fixedSubgroup.normalizerMonoidHom
    ⟨g, a.fixedSubgroup.le_normalizer hg⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact mem_map.mpr ⟨f y,
    map_pResidual_le 2 f.toMonoidHom (mem_map.mpr ⟨y, hy, rfl⟩), rfl⟩

/-- A component upstairs maps onto a quasisimple two-residual of the full
fixed subgroup downstairs. -/
theorem component_image_eq_fixedTwoResidual (a : MulAut K) (L : Subgroup K)
    (hL : IsComponentIn L a.fixedSubgroup)
    [IsQuasisimple (fixedTwoResidual ((center K).quotientAut a))] :
    L.map (QuotientGroup.mk' (center K)) =
      fixedTwoResidual ((center K).quotientAut a) := by
  let q := QuotientGroup.mk' (center K)
  let b := (center K).quotientAut a
  let R := fixedTwoResidual b
  have hRperfect : Group.IsPerfect (pResidual 2 b.fixedSubgroup) := by
    exact Group.IsPerfect.ofSurjective
      (f := ((pResidual 2 b.fixedSubgroup).equivMapOfInjective
        b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective).symm.toMonoidHom)
      ((pResidual 2 b.fixedSubgroup).equivMapOfInjective
        b.fixedSubgroup.subtype b.fixedSubgroup.subtype_injective).symm.surjective
  let := hRperfect
  have hres : solvableResidual b.fixedSubgroup = pResidual 2 b.fixedSubgroup := by
    let : Group.IsNilpotent (b.fixedSubgroup ⧸ pResidual 2 b.fixedSubgroup) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
      (le_solvableResidual_of_isPerfect _)
  obtain ⟨F, hFperfect, hFa, hFq⟩ := exists_perfect_fixed_lift (MulEquiv.refl _) a
  have hb : centralQuotientAction (MulEquiv.refl (K ⧸ center K)) a = b := by
    ext x
    rfl
  have hFR : F.map q = R := by
    change F.map q = fixedPerfectResidual
      (centralQuotientAction (MulEquiv.refl (K ⧸ center K)) a) at hFq
    rw [hb] at hFq
    change F.map q = (solvableResidual b.fixedSubgroup).map b.fixedSubgroup.subtype at hFq
    rwa [hres] at hFq
  let := hFperfect
  let : IsQuasisimple (F.map q) := hFR.symm ▸ inferInstance
  let f : PerfectCentralCovering.Cover F (F.map q) := {
    toMonoidHom := q.subgroupMap F
    surjective := q.subgroupMap_surjective F
    isPerfect := hFperfect
    ker_le_center := by
      intro x hx
      have hxZ : (x : K) ∈ center K := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact congrArg Subtype.val hx
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp hxZ y) }
  let : IsQuasisimple F := f.isQuasisimple
  let := hL.quasisimple
  let : Group.IsPerfect (L.map q) := Group.IsPerfect.map q
  have hLb : L.map q ≤ b.fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup, quotientAut_apply_mk,
      (mem_fixedSubgroup a x).mp (hL.1 hx)]
  have hLR : L.map q ≤ F.map q := by
    rw [hFR]
    change L.map q ≤ (pResidual 2 b.fixedSubgroup).map b.fixedSubgroup.subtype
    rw [← hres]
    exact le_map_solvableResidual_of_isPerfect _ _ hLb
  have hLF : L ≤ F := perfect_le_of_map_le_of_central_kernel q
    (by rw [QuotientGroup.ker_mk']) L F hLR
  have hc := hL.restrict hLF hFa
  have ht : IsComponent F (⊤ : Subgroup F) :=
    ⟨.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have he : L = F := le_antisymm hLF (subgroupOf_eq_top.mp (hc.2.eq_of_le ht le_top))
  exact he ▸ hFR
/-- A lift of any fixed quotient element normalizes the original component,
provided the quotient fixed subgroup has quasisimple two-residual. -/
theorem mem_normalizer_of_quotient_fixed (a : MulAut K) (L : Subgroup K)
    (hL : IsComponentIn L a.fixedSubgroup)
    [IsQuasisimple (fixedTwoResidual ((center K).quotientAut a))]
    (u : K) (hu : QuotientGroup.mk' (center K) u ∈
      ((center K).quotientAut a).fixedSubgroup) : u ∈ normalizer (L : Set K) := by
  let := hL.quasisimple
  rw [← comap_normalizer_map_eq_of_perfect (QuotientGroup.mk' (center K))
    (by rw [QuotientGroup.ker_mk']) L]
  change QuotientGroup.mk' (center K) u ∈ normalizer
    (L.map (QuotientGroup.mk' (center K)) : Set (K ⧸ center K))
  rw [component_image_eq_fixedTwoResidual a L hL]
  exact fixed_le_normalizer_fixedTwoResidual _ hu

end MulAut
