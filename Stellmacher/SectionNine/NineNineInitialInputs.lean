module

public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer

/-!
# Initial action and predecessor containment for Stellmacher (9.9)

The initial center acts nontrivially on the terminal neighbor-center module:
otherwise the proved ambient module-centralizer bound contradicts criticality.
For distance greater than three, any neighbor module at a predecessor of the
initial vertex lies in the first-step core. A three-edge path and critical
minimality suffice, and yield normalization of the first-step center.

These inputs retain Hypothesis Two on the ambient group H. They do not prove
the reversed (9.8) application or the support selection in (9.9)(1).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_nine_initial_action_nontrivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ := by
  obtain ⟨actor, _, hactor⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcentralizer := nine_three_module_centralizer_core_at_vertex ctx
    ctx.criticalPath.a' ⟨actor, hactor⟩
  intro htrivial
  exact ctx.criticalPath.critical.2
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp htrivial).trans hcentralizer)

public theorem nine_nine_previous_module_le_first_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    VAt ctx.Γ previous ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  let path : Fin 4 → ctx.Γ.Vertex :=
    ![neighbor, previous, ctx.criticalPath.a, ctx.criticalPath.firstStep]
  have hadj : ∀ index : Fin 3,
      ctx.Γ.adjacent (path index.castSucc) (path index.succ) := by
    intro index
    fin_cases index
    · exact ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor)
    · exact ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hprevious)
    · exact ctx.criticalPath.firstStep_adj
  have hdistance : ctx.Γ.distance neighbor ctx.criticalPath.firstStep ≤ 3 :=
    ctx.Γ.distance_le_of_path 3 path hadj
  exact critical_minimality ctx.Γ ctx.criticalPath (hdistance.trans_lt hb)

public theorem nine_nine_previous_normalizes_first_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    VAt ctx.Γ previous ≤
      Subgroup.normalizer (ZAt ctx.Γ ctx.criticalPath.firstStep : Set G) := by
  have hcore : QAt ctx.Γ ctx.criticalPath.firstStep ≤
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤
      ctx.Γ.vertexStabilizer ctx.criticalPath.firstStep
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  exact (nine_nine_previous_module_le_first_core ctx hb previous hprevious).trans
    (hcore.trans (stabilizer_le_normalizer_z_public ctx.Γ ctx.criticalPath.firstStep))

end Stellmacher.SectionNine
