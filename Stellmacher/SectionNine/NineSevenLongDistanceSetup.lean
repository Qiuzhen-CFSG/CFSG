module

public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs

/-!
# Genuine commutator and neighborhood-join inputs for (9.7)

The ambient module-centralizer bound makes [V_terminal,Z_initial]
nontrivial. The mutual module normalizers and quadratic actions from (7.4)
and (7.5) put this commutator in both modules and centralizers; critical
minimality puts it in the second and penultimate cores. These are core
containments, not the stronger center containments still required in (9.7).

The source's U is the join of W at neighbors of the initial vertex, with
W expressed by GeneratedNeighborhoodV. Six-edge walks put any two of its
center generators in commuting positions when b>6. The same walk bound
puts U in the core at every neighbor of the second path vertex.

The final equivalence isolates the numerical use of the proved odd distance
in (7.5). This module does not claim the exclusion of b>=7 or (9.7).
Source: Stellmacher, printed pp.53--54 / PDF pp.43--44 of
refs/files/stellmacher-n-group.pdf, before the distance-five paragraph.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem nine_seven_terminal_initial_commutator_ne_bot
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≠ ⊥ := by
  obtain ⟨actor, _, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcentral := nine_three_module_centralizer_core_at_vertex ctx
    ctx.criticalPath.a' ⟨actor, hterminal⟩
  intro hcomm
  apply ctx.criticalPath.critical.2
  exact (Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans hcentral

public theorem nine_seven_terminal_initial_commutator_le_modules
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  have hcontain := lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hfirst := (Subgroup.le_normalizer_iff_commutator_le_right.mp
    (hcontain.reverse_containment.2.trans
      (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep)))
  have hterminal := (Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((hcontain.first_containment.1.trans hcontain.first_containment.2).trans
      (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')))
  refine le_inf ((Subgroup.commutator_mono le_rfl hcontain.first_containment.1).trans
    hfirst) ?_
  rw [Subgroup.commutator_comm]
  exact hterminal

public theorem nine_seven_terminal_initial_commutator_centralizes_modules
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) ⊓
        Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) := by
  have hcontain := lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hquadratic := (lemma_seven_five ctx.sectionSeven ctx.Γ
    ctx.criticalPath ctx.commutator_eq).longer_case hb
  have hcomm : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', VAt ctx.Γ ctx.criticalPath.firstStep⁆ :=
    Subgroup.commutator_mono le_rfl hcontain.first_containment.1
  refine le_inf (hcomm.trans
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hquadratic.2.1)) ?_
  have hreverse := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hquadratic.2.2
  rw [Subgroup.commutator_comm (VAt ctx.Γ ctx.criticalPath.firstStep)] at hreverse
  exact hcomm.trans hreverse

public theorem nine_seven_terminal_initial_commutator_le_penultimate_core
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      QAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩) := by
  exact ((nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_left).trans
    (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1

public theorem nine_seven_terminal_initial_commutator_le_second_core
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      QAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) := by
  exact ((nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_right).trans
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1

private theorem three_neighbor_join_le
    (Γ : CosetGraphContext G T A B) (initial : Γ.Vertex) (target : Subgroup G)
    (hcenters : ∀ first, first ∈ Neighborhood Γ initial →
      ∀ second, second ∈ Neighborhood Γ first →
      ∀ third, third ∈ Neighborhood Γ second →
      ZAt Γ third ≤ target) :
    sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Γ initial ∧
      subgroup = GeneratedNeighborhoodV Γ neighbor} ≤
        target := by
  apply sSup_le
  rintro subgroup ⟨first, hfirst, rfl⟩
  rw [GeneratedNeighborhoodV]
  apply sSup_le
  rintro subgroup ⟨second, hsecond, rfl⟩
  rw [Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨third, hthird, rfl⟩
  exact hcenters first hfirst second hsecond third hthird

public theorem nine_seven_initial_neighbor_join_abelian
    (ctx : SectionNineLocalContext G T A B) (hb : 6 < ctx.criticalPath.length) :
    let initialJoin := sSup {subgroup : Subgroup G |
      ∃ neighbor, neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor}
    ⁅initialJoin, initialJoin⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  apply three_neighbor_join_le
  intro leftFirst hleftFirst leftSecond hleftSecond leftThird hleftThird
  apply Subgroup.le_centralizer_iff.mpr
  apply three_neighbor_join_le
  intro rightFirst hrightFirst rightSecond hrightSecond rightThird hrightThird
  have hleftFirstAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hleftFirst
  have hleftSecondAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hleftSecond
  have hleftThirdAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hleftThird
  have hrightFirstAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hrightFirst
  have hrightSecondAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hrightSecond
  have hrightThirdAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hrightThird
  let vertices : Fin 7 → ctx.Γ.Vertex :=
    ![rightThird, rightSecond, rightFirst, ctx.criticalPath.a,
      leftFirst, leftSecond, leftThird]
  have hwalk : ∀ step : Fin 6,
      ctx.Γ.adjacent (vertices step.castSucc) (vertices step.succ) := by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hrightThirdAdj
    · exact ctx.Γ.adjacent_symm hrightSecondAdj
    · exact ctx.Γ.adjacent_symm hrightFirstAdj
    · exact hleftFirstAdj
    · exact hleftSecondAdj
    · exact hleftThirdAdj
  have hdist := ctx.Γ.distance_le_of_path 6 vertices hwalk
  change ctx.Γ.distance rightThird leftThird ≤ 6 at hdist
  have hcore := critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)
  have hneighbor : leftSecond ∈ Neighborhood ctx.Γ leftThird :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hleftThirdAdj)
  have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    leftThird leftSecond hneighbor
  exact hcore.trans (Subgroup.le_centralizer_iff.mp
    (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))))

public theorem nine_seven_initial_neighbor_join_le_neighbor_core
    (ctx : SectionNineLocalContext G T A B) (hb : 6 < ctx.criticalPath.length)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ
      (ctx.criticalPath.path ⟨2, by omega⟩)) :
    sSup {subgroup : Subgroup G |
      ∃ vertex, vertex ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ vertex} ≤ QAt ctx.Γ neighbor := by
  apply three_neighbor_join_le
  intro first hfirst second hsecond third hthird
  have hfirstAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hfirst
  have hsecondAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hsecond
  have hthirdAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hthird
  have hneighborAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  have hpathAdj : ctx.Γ.adjacent ctx.criticalPath.firstStep
      (ctx.criticalPath.path ⟨2, by omega⟩) := by
    have hedge := ctx.criticalPath.path_adj ⟨1, by omega⟩
    change ctx.Γ.adjacent (ctx.criticalPath.path ⟨1, by omega⟩)
      (ctx.criticalPath.path ⟨2, by omega⟩) at hedge
    rwa [ctx.criticalPath.path_first] at hedge
  let vertices : Fin 7 → ctx.Γ.Vertex :=
    ![third, second, first, ctx.criticalPath.a, ctx.criticalPath.firstStep,
      ctx.criticalPath.path ⟨2, by omega⟩, neighbor]
  have hwalk : ∀ step : Fin 6,
      ctx.Γ.adjacent (vertices step.castSucc) (vertices step.succ) := by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hthirdAdj
    · exact ctx.Γ.adjacent_symm hsecondAdj
    · exact ctx.Γ.adjacent_symm hfirstAdj
    · exact ctx.criticalPath.firstStep_adj
    · exact hpathAdj
    · exact hneighborAdj
  have hdist := ctx.Γ.distance_le_of_path 6 vertices hwalk
  change ctx.Γ.distance third neighbor ≤ 6 at hdist
  exact critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)

public theorem nine_seven_length_le_five_iff_no_long_distance
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ctx.criticalPath.length ≤ 5 ↔ ¬ 7 ≤ ctx.criticalPath.length := by
  obtain ⟨half, hhalf⟩ := (lemma_seven_five ctx.sectionSeven ctx.Γ
    ctx.criticalPath ctx.commutator_eq).odd_distance
  omega

end Stellmacher.SectionNine
