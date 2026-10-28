module
public import Stellmacher.SectionTen.TenOneSmallPrimitiveCentralizer
public import Theory.GroupTheory.C4SquareInvolutionBound


/-!
# Fixed points of middle-core subgroups of index at most two

In the actual small first-module case, the centralizer in Wstar of any
subgroup of index at most two in the middle two-core lies in the middle
center. The subgroup is supplied on the literal core carrier and mapped
back through its subtype; no ambient action or cardinality branch is changed.

Its intersection with the residual core has index at most two in that
order-sixteen C4-square group. Hence the intersection has more than four
points and contains an element with nontrivial square. The proved primitive
point centralizer in Wstar is exactly the middle center, so centralizing
the whole supplied subgroup forces membership in that center.

Source: Stellmacher (10.1)(a3), printed pp.61–62, the application of (1.2)
in assertion (9), `refs/files/stellmacher-n-group.pdf`. This isolates the
fixed-point containment used by the subsequent actual quadratic closure.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_coatom_centralizer_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (F : Subgroup (QAt ctx.Γ middle)) (hF : F.index ≤ 2) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Wstar ⊓ Subgroup.centralizer (F.map (QAt ctx.Γ middle).subtype : Set G) ≤
      ZAt ctx.Γ middle := by
  let Q := QAt ctx.Γ middle
  let D := twoCoreIn (EAt ctx.Γ middle)
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  let DQ := D.subgroupOf Q
  let I := F.subgroupOf DQ
  have hIindex : I.index ≤ 2 := by
    have hh := Subgroup.relIndex_le_of_le_right (H:=F) (show DQ≤⊤ from le_top)
      (show F.relIndex ⊤ ≠ 0 by rw [Subgroup.relIndex_top_right]; exact F.index_ne_zero_of_finite)
    rw [Subgroup.relIndex_top_right] at hh
    exact hh.trans hF
  have hDcard : Nat.card DQ = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv]
    exact ten_one_middle_residual_core_card ctx middle hpath hsmall hmodel
  have hIcard : 4 < Nat.card I := by
    have hh := I.index_mul_card
    rw [hDcard] at hh
    nlinarith
  have hDmodel : Nonempty (DQ ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
    obtain ⟨e⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    exact ⟨(Subgroup.subgroupOfEquivOfLe hDQ).trans e⟩
  obtain ⟨x,hx,hx2⟩ := Subgroup.exists_square_ne_one_of_c4_square_card_gt_four hDmodel I hIcard
  have hxD : ((x:Q):G) ∈ D := x.property
  have hxF : ((x:Q):G) ∈ F.map Q.subtype := ⟨x,hx,rfl⟩
  have hxG2 : ((x:Q):G)^2 ≠ 1 := by
    intro heq
    exact hx2 (Subtype.ext (Subtype.ext heq))
  have hc := ten_one_small_primitive_wstar_centralizer ctx middle hpath hsmall hmodel
    ((x:Q):G) hxD hxG2
  dsimp only at hc ⊢
  rw [← hc]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxF))

end Stellmacher.SectionTen

