module
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Stellmacher.SectionTen.TenOneSmallNeighborCore
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Saturating the residual core from neighborhood commutators

In the actual Section Ten offset-two configuration with first local quotient
SL2(2), any first-stabilizer-invariant subgroup containing the commutator of
the first residual core and the generated middle neighborhood contains the
entire residual core. The subgroup need not itself lie inside the core.

The literal action on the residual core modulo its intersection with the
given subgroup kills the neighborhood. That neighborhood is a two-group
escaping the first core, so the S3 normal-kernel lemma forces a two-group
action quotient. The first two-residual therefore acts trivially. The
residual-core commutator identity then forces the asserted containment.

This is the saturation step for the normal closure of the order-two
displacement line in Stellmacher (10.1)(a), Journal of Algebra 190 (1997),
printed p.60. It requires no small-module cardinality or desired quotient
cardinality and preserves the actual conjugation action throughout.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_residual_action_saturation
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (K : Subgroup G)
    (hPK : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
      GeneratedNeighborhoodV ctx.Γ middle⁆ ≤ K) :
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤ K := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn E
  let V := K
  let U := GeneratedNeighborhoodV ctx.Γ middle
  have hE : E = twoResidualIn P := by
    change ctx.Γ.twoResidualAt ctx.criticalPath.firstStep = _
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := hPK
  have hN : (V.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRP.trans hPV)
  let _ := hN
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action P R V hPR hPV hN
  have hUK : U.subgroupOf P ≤ action.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P R V U hN hPR hcomm
      action haction
  obtain ⟨_, hfirst, hterminal, hdistinct⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUcore : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ P := hUcore.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
      ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hUtwo : IsPGroup 2 U :=
    nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ middle U hUcore
  have hUnot : ¬ U ≤ Q := by
    intro hle
    apply ten_one_neighbor_module_not_le_core ctx middle hpath hterminal hfirst hdistinct.symm
    exact (show VAt ctx.Γ ctx.criticalPath.a' ≤ U from
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal, rfl⟩).trans hle
  have hQtwo : IsPGroup 2 (Q.subgroupOf P) := by
    have hQ : Q = twoCoreIn P := by
      change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep = _
      rw [ctx.Γ.twoCoreAt_def]
      rfl
    rw [hQ, twoCoreIn, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      P.subtype_injective]
    exact pCore_isPGroup
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  obtain ⟨equiv⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f := equiv.toMonoidHom.comp projection
  have hquot : IsPGroup 2 (P ⧸ action.ker) :=
    Subgroup.quotient_isPGroup_two_of_perm_three_normal_kernel
      (Q.subgroupOf P) action.ker (U.subgroupOf P) hQtwo f
      (equiv.surjective.comp hsurj)
      (by dsimp only [f]; rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective]; exact hker)
      (hUtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hUP).symm) hUK (by
        intro hle
        apply hUnot
        intro element helement
        exact hle (show (⟨element, hUP helement⟩ : P) ∈ U.subgroupOf P from helement))
  have hres : twoResidualSubgroup P ≤ action.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le action.ker inferInstance hquot
  have hEK : E ≤ action.ker.map P.subtype := by
    rw [hE, twoResidualIn, twoResidualAmbient]
    exact Subgroup.map_mono hres
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm
        ctx.criticalPath.firstStep_adj)) P le_rfl
  have hcore : R = ⁅R, E⁆ := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  change R ≤ V
  rw [hcore, Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro actor hactor vector hvector
  obtain ⟨a, ha, rfl⟩ := hEK hactor
  let vectorR : R := ⟨vector, hvector⟩
  have hfix : action a (QuotientGroup.mk' (V.subgroupOf R) vectorR) =
      QuotientGroup.mk' (V.subgroupOf R) vectorR := by
    rw [show action a = 1 from ha]
    rfl
  rw [haction] at hfix
  have hmem := QuotientGroup.eq_iff_div_mem.mp hfix
  change (a : G) * vector * (a : G)⁻¹ / vector ∈ V at hmem
  change ⁅(a : G), vector⁆ ∈ V
  simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
end Stellmacher.SectionTen


