module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleComparison
public import Theory.SpecificGroups.Alternating.FiveNormalSectionOddOvergroups

/-!
# The single alternating-five comparison

Normality of K = O²(H) allows the intrinsic normal-section bound to apply
to the original overlap H ∩ M. The prescribed odd Hall is therefore a
three-group, regardless of the containing component's model. This does
not assert Hall placement. The final moving-Hall source assembly consumes
this bound directly.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- A single A₅ comparison gives the original Hall bound directly.
Its normality is in H, and the proper overlap is the original H ∩ M. -/
theorem ComparisonConfiguration.hall_isThreeGroup_of_single_a5
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (e : (c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) :
    IsPGroup 3 B := by
  let : c.component.Normal := hsingle.symm ▸ inferInstance
  have hS : (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    intro x hx
    exact le_normalizer_componentOrbit L T hx
  have hproper : D.maximalLocal.subgroupOf H ≠ ⊤ :=
    fun he => ctx.hstar.1.2 (subgroupOf_eq_top.mp he)
  exact Theory.SpecificGroups.Alternating.FiveSylowMaximal.normal_section_odd_subgroup_isThreeGroup
    (T.subtype ctx.hstar.1.1.2) c.component e c.generates
    (D.maximalLocal.subgroupOf H) B hS hproper ctx.hall_le ctx.hall_odd
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
