module
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Stellmacher.SectionTen.TenOneResidualKernelCoreTransfer
public import Stellmacher.SectionTen.TenOneSmallNeighborCore
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Nontrivial residual-core action on the middle neighborhood

For the actual offset-two configuration of Section Ten, suppose that the
first stabilizer modulo its two-core is SL2(2). Its residual two-core does
not commute with the generated middle neighborhood modulo the first module.
This is the nontriviality step in the small branch of Stellmacher (10.1),
Journal of Algebra 190 (1997), printed page 60.

The residual quotient-action kernel transfer puts the neighborhood inside
the first two-core if this commutator containment holds. The neighborhood
is a two-group in the first stabilizer, while its terminal module escapes
the first core by the actual critical geometry. These facts contradict the
containment. The imported transfer uses the S3 normal-kernel theorem and
the already proved noncentral action of the first residual on its own core;
this consumer does not require the small-branch module cardinality.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_core_neighborhood_not_le_module
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
        GeneratedNeighborhoodV ctx.Γ middle⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let U := GeneratedNeighborhoodV ctx.Γ middle
  intro hcomm
  obtain ⟨_,hfirst,hterminal,hdistinct⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUcore : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ GAt ctx.Γ ctx.criticalPath.firstStep := hUcore.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
      ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hUtwo : IsPGroup 2 U :=
    nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ middle U hUcore
  have hUfirst : U ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    ten_one_two_subgroup_le_first_core_of_residual_commutator ctx middle hpath hmodel
      U hUP hUtwo (by rw [Subgroup.commutator_comm]; exact hcomm)
  apply ten_one_neighbor_module_not_le_core ctx middle hpath hterminal hfirst hdistinct.symm
  exact (show VAt ctx.Γ ctx.criticalPath.a' ≤ U from
    le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩).trans hUfirst

end Stellmacher.SectionTen
