module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Regular
public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Morphism.CodRestrict
/-!
# Restricting a semiregular cocharacter to a closed overgroup

If a closed subgroup contains the original torus, the original cocharacter
factors through the literal inverse image of that torus under inclusion.
An element of the subgroup centralizes this cocharacter precisely when its
ambient image does. Thus equality of the cocharacter and torus centralizers
passes to the original closed subgroup, with the actual inclusion maps.

This is the hereditary regularity step used in Borel, *Linear Algebraic
Groups*, IV, 13.1 and 13.11(2), specialized for the construction in 13.12.
The intended overgroups are the two subtorus centralizers.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

theorem semiregular_cocharacter_restriction
    (T H : ClosedSubgroup G) (hTH : T ≤ H) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer) :
    let Ti := H.inclusion.closedSubgroupPreimage T
    letI : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    ∃ cH : ClosedSubgroupTorusCocharacter Ti,
      (∀ t : Variety.Point (KMult k),
        H.inclusion.onPoints (Ti.includePoint
          (cH.onPoints t)) = T.includePoint (c.onPoints t)) ∧
      (Ti.inclusion.comp cH).imageClosedSubgroup.centralizer = Ti.centralizer := by
  dsimp only
  let _ : AlgebraicGroup (H.inclusion.closedSubgroupPreimage T).carrierVariety :=
    (H.inclusion.closedSubgroupPreimage T).carrierAlgebraicGroup
  let Ti := H.inclusion.closedSubgroupPreimage T
  let f := (T.inclusion.comp c).codRestrictClosedSubgroup H
    (fun t => hTH (T.pointEquiv (c.onPoints t)).property)
  have hf (t : Variety.Point (KMult k)) : H.inclusion.onPoints (f.onPoints t) =
      T.includePoint (c.onPoints t) :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hfT (t : Variety.Point (KMult k)) : f.onPoints t ∈ Ti := by
    change H.inclusion.onPoints (f.onPoints t) ∈ T
    rw [hf]
    exact (T.pointEquiv (c.onPoints t)).property
  let cH := f.codRestrictClosedSubgroup Ti hfT
  have hi (t : Variety.Point (KMult k)) : Ti.inclusion.onPoints (cH.onPoints t) = f.onPoints t :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _
  have hcomp (t : Variety.Point (KMult k)) :
      H.inclusion.onPoints (Ti.includePoint (cH.onPoints t)) = T.includePoint (c.onPoints t) := by
    change H.inclusion.onPoints (Ti.inclusion.onPoints (cH.onPoints t)) = _
    rw [hi, hf]
  refine ⟨cH, hcomp, SetLike.coe_injective ?_⟩
  ext x
  constructor
  · intro hx
    have hxG : H.inclusion.onPoints x ∈ (T.inclusion.comp c).imageClosedSubgroup.centralizer := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro y ⟨t, rfl⟩
      have hh := Subgroup.mem_centralizer_iff.mp hx _ (show
        Ti.includePoint (cH.onPoints t) ∈ (Ti.inclusion.comp cH).imageClosedSubgroup from ⟨t, rfl⟩)
      have he := congrArg H.inclusion.onPoints hh
      change T.includePoint (c.onPoints t) * H.inclusion.onPoints x =
        H.inclusion.onPoints x * T.includePoint (c.onPoints t)
      simpa only [map_mul, hcomp] using he
    rw [hc] at hxG
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    apply H.inclusion_injective
    exact (by simpa only [map_mul] using
      (Subgroup.mem_centralizer_iff.mp hxG (H.inclusion.onPoints t) ht))
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    rintro t ⟨u, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hx _ (Ti.pointEquiv (cH.onPoints u)).property
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
