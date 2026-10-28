module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneFixedSpace
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.GlobalOffender.Source

/-!
# The sole surviving component section in the original residual action

The original component maps onto its literal image in the global offender
subgroup. The original generator of V₁ is fixed by its Sylow two-subgroup,
and its stabilizer is a two-group. These facts survive the same quotient
map. The cubic-fixer alternatives of B.5 therefore contradict that actual
stabilizer, leaving only a natural SL₂ section over a binary field.

This is an output restriction, not a new premise. The genuine earlier
alternating-five constituent excludes the remaining row in the subsequent
comparison; no splitting of the original module is required here.
Source: Aschbacher–Smith 14.7.67(4), printed p.1070.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer ResidualNormalizer.Components
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

def residualOffenderGlobalEquiv
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    residualOffenderComponent (L := L) (F := F) B ≃* d.residualGlobalComponent hs B := by
  let := (d.residualSpan_reduced hs).elementary
  exact (subgroupOfEquivOfLe (residualOffenderComponentPlus_le_actor (L := L) (F := F))).trans
    (subgroupOfEquivOfLe (d.residual_component_le_globalOffender earlier hs hB)).symm

def residualComponentToGlobal
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    B →* d.residualGlobalComponent hs B := by
  let := (d.residualSpan_reduced hs).elementary
  exact (d.residualOffenderGlobalEquiv earlier hs hB).toMonoidHom.comp
    (residualComponentToOffender hB)

theorem residualComponentToGlobal_surjective
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    Function.Surjective (d.residualComponentToGlobal earlier hs hB) := by
  let := (d.residualSpan_reduced hs).elementary
  exact (d.residualOffenderGlobalEquiv earlier hs hB).surjective.comp
    (residualComponentToOffender_surjective hB)

theorem residualComponentToGlobal_equivariant
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (b : B) (v : Additive ((E F).subgroupOf (Y L F))) :
    let := (d.residualSpan_reduced hs).elementary
    d.residualComponentRepresentation hs (hB.1.trans J_le_Y) b v =
      d.residualGlobalAction hs ((d.residualGlobalComponent hs B).subtype
        (d.residualComponentToGlobal earlier hs hB b)) v := by
  let := (d.residualSpan_reduced hs).elementary
  rfl

theorem residualGlobalComponent_not_cubicFixed
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    ¬ RankOneFixedSpace.CubicFixed
      ((d.residualGlobalAction hs).comp (d.residualGlobalComponent hs B).subtype) := by
  let := (d.residualSpan_reduced hs).elementary
  dsimp only
  intro h
  let q := d.residualComponentToGlobal earlier hs hB
  have hq := d.residualComponentToGlobal_surjective earlier hs hB
  let σ := d.residualComponentRepresentation hs (hB.1.trans J_le_Y)
  let τ := (d.residualGlobalAction hs).comp (d.residualGlobalComponent hs B).subtype
  let z := d.residualPointVector
  obtain ⟨P,hP⟩ := d.residual_component_point_fixed_by_sylow hs hB
  have hz : z ∈ fixedSpace τ (P.mapSurjective hq : Subgroup _) := by
    rintro ⟨a,ha⟩
    rw [Sylow.coe_mapSurjective] at ha
    obtain ⟨b,hb,rfl⟩ := ha
    exact (d.residualComponentToGlobal_equivariant earlier hs hB b z).symm.trans (hP hb)
  obtain ⟨a,ha,h3,hfix⟩ := h (P.mapSurjective hq)
  have hp : IsPGroup 2 (pointStabilizer σ z) := by
    have he := d.residual_component_point_stabilizer_residual_eq_bot hs hB
    exact (isPGroup_quotient_pResidual (G := pointStabilizer σ z) 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)
  have hn : a ≠ 1 := fun he => ha (he ▸ (P.mapSurjective hq).one_mem)
  apply cubic_not_mem_twoSubgroup ((pointStabilizer σ z).map q) (hp.map q) a h3 hn
  obtain ⟨b,rfl⟩ := hq a
  refine ⟨b,?_,rfl⟩
  exact (d.residualComponentToGlobal_equivariant earlier hs hB b z).trans (hfix z hz)

theorem residualGlobalComponent_linearTwo
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hs).elementary
    ∀ c : ProjectiveLine.QuasisimpleSourceConclusion
      (d.residualGlobalAction hs) (d.residualGlobalComponent hs B),
    ∃ k : BinaryField, Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
      (c.sectionData.action.comp (d.residualGlobalComponent hs B).subtype)
      (ChapterB.QuasisimpleSource.linearNatural k 2)) := by
  let := (d.residualSpan_reduced hs).elementary
  dsimp only
  intro c
  exact (RankOneFixedSpace.linearTwo_or_cubic
    (c.rank_one_action (d.residualGlobalOffender_threeRank hs))).resolve_right
    (d.residualGlobalComponent_not_cubicFixed earlier hs hB)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
