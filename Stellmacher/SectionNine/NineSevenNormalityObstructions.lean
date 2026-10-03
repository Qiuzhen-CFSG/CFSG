module

public import Stellmacher.SectionNine.NineSevenCentralizerCore

/-!
# Forbidden normality in the large-distance branches of (9.7)

The actual neighbor-center modules, neighborhood joins W, and the join U of
neighboring W groups lie in vertex two-cores by critical minimality. Their
own stabilizers normalize them. Invariance under the other endpoint of an
edge would make them normal two-subgroups of G, whose two-core is trivial.
The final ambient package establishes nontriviality from the initial center
of order four and excludes all four normality outcomes used in the source.

This module does not prove that any forbidden normality outcome occurs;
the terminal-containment branches still require their commutator arguments.
Source: Stellmacher, printed p.54 / PDF p.44, from “Assume that U” through
the paragraph preceding the distance-five case, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

public theorem nine_seven_edge_invariant_two_subgroup_eq_bot
    (h7 : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    {left right : Γ.Vertex} (hadj : Γ.adjacent left right)
    (subgroup : Subgroup G) (htwo : IsPGroup 2 subgroup)
    (hleft : GAt Γ left ≤ Subgroup.normalizer (subgroup : Set G))
    (hright : GAt Γ right ≤ Subgroup.normalizer (subgroup : Set G)) :
    subgroup = ⊥ := by
  have hgen := (edge_sectionThree_data h7 Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr hadj) default).2.2.2.2.1
  have hnormal : subgroup.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hleft hright
  have hcore : subgroup ≤ pCore 2 G := le_sSup ⟨hnormal, htwo⟩
  rw [h7.twoCore_eq_bot] at hcore
  exact le_bot_iff.mp hcore

public theorem nine_seven_module_le_own_core
    (ctx : SectionNineLocalContext G T A B) (hb : 1 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex) : VAt ctx.Γ vertex ≤ QAt ctx.Γ vertex := by
  change ctx.Γ.vAt vertex ≤ _
  rw [ctx.Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  have hdist := ctx.Γ.distance_le_of_path 1 ![neighbor, vertex] (by
    intro step
    fin_cases step
    exact ctx.Γ.adjacent_symm hadj)
  exact critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)

public theorem nine_seven_neighborhood_le_own_core
    (ctx : SectionNineLocalContext G T A B) (hb : 2 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex) : GeneratedNeighborhoodV ctx.Γ vertex ≤ QAt ctx.Γ vertex := by
  rw [GeneratedNeighborhoodV]
  apply sSup_le
  rintro subgroup ⟨neighbor, hneighbor, rfl⟩
  rw [ctx.Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨other, hother, rfl⟩
  have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  have hadj' := (mem_neighborhood_iff_adjacent ctx.Γ).mp hother
  have hdist := ctx.Γ.distance_le_of_path 2 ![other, neighbor, vertex] (by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hadj'
    · exact ctx.Γ.adjacent_symm hadj)
  exact critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)

public theorem nine_seven_subgroup_isTwoGroup_of_le_vertex_core
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) (subgroup : Subgroup G)
    (hle : subgroup ≤ QAt Γ vertex) : IsPGroup 2 subgroup := by
  have hcore : IsPGroup 2 (QAt Γ vertex) := by
    change IsPGroup 2 (Γ.twoCoreAt vertex)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt Γ vertex)).map _
  exact hcore.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

public theorem nine_seven_module_not_normalized_by_neighbor
    (ctx : SectionNineLocalContext G T A B) (hb : 1 < ctx.criticalPath.length)
    {vertex neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent vertex neighbor)
    (hne : VAt ctx.Γ vertex ≠ ⊥) :
    ¬ GAt ctx.Γ neighbor ≤ Subgroup.normalizer (VAt ctx.Γ vertex : Set G) := by
  intro hnormal
  exact hne (nine_seven_edge_invariant_two_subgroup_eq_bot ctx.sectionSeven ctx.Γ hadj
    (VAt ctx.Γ vertex) (nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ vertex _
      (nine_seven_module_le_own_core ctx hb vertex))
    (stabilizer_le_normalizer_v ctx.Γ vertex) hnormal)

public theorem nine_seven_neighborhood_not_normalized_by_neighbor
    (ctx : SectionNineLocalContext G T A B) (hb : 2 < ctx.criticalPath.length)
    {vertex neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent vertex neighbor)
    (hne : GeneratedNeighborhoodV ctx.Γ vertex ≠ ⊥) :
    ¬ GAt ctx.Γ neighbor ≤
      Subgroup.normalizer (GeneratedNeighborhoodV ctx.Γ vertex : Set G) := by
  intro hnormal
  exact hne (nine_seven_edge_invariant_two_subgroup_eq_bot ctx.sectionSeven ctx.Γ hadj
    (GeneratedNeighborhoodV ctx.Γ vertex)
    (nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ vertex _
      (nine_seven_neighborhood_le_own_core ctx hb vertex))
    (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ vertex) hnormal)

public theorem nine_seven_neighborhood_act
    (Γ : CosetGraphContext G T A B) (actor : G) (vertex : Γ.Vertex) :
    GeneratedNeighborhoodV Γ (Γ.act actor vertex) =
      (GeneratedNeighborhoodV Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom := by
  have hle (actor : G) (vertex : Γ.Vertex) :
      (GeneratedNeighborhoodV Γ vertex).map (MulAut.conj actor⁻¹).toMonoidHom ≤
        GeneratedNeighborhoodV Γ (Γ.act actor vertex) := by
    rw [Subgroup.map_le_iff_le_comap, GeneratedNeighborhoodV]
    apply sSup_le
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    apply Subgroup.map_le_iff_le_comap.mp
    change (v Γ neighbor).map _ ≤ _
    rw [← v_act]
    apply le_sSup
    exact ⟨Γ.act actor neighbor, (mem_neighborhood_iff_adjacent Γ).mpr
      (adjacent_act Γ actor ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)), rfl⟩
  apply le_antisymm ?_ (hle actor vertex)
  have hback := Subgroup.map_mono (f := (MulAut.conj actor⁻¹).toMonoidHom)
    (hle actor⁻¹ (Γ.act actor vertex))
  have hcomp : (MulAut.conj actor⁻¹).toMonoidHom.comp
      (MulAut.conj actor).toMonoidHom = MonoidHom.id G := by
    ext element
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one, inv_inv,
    Subgroup.map_map, hcomp, Subgroup.map_id] using hback

public theorem nine_seven_stabilizer_normalizes_neighbor_join
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) :
    GAt Γ vertex ≤ Subgroup.normalizer
      ((sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Γ vertex ∧
        subgroup = GeneratedNeighborhoodV Γ neighbor} : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hmap : (sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood Γ vertex ∧ subgroup = GeneratedNeighborhoodV Γ neighbor}).map
        (MulAut.conj actor).toMonoidHom ≤
      sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Γ vertex ∧
        subgroup = GeneratedNeighborhoodV Γ neighbor} := by
    rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    apply Subgroup.map_le_iff_le_comap.mp
    have heq := nine_seven_neighborhood_act Γ actor⁻¹ neighbor
    simp only [inv_inv] at heq
    rw [← heq]
    apply le_sSup
    refine ⟨Γ.act actor⁻¹ neighbor, ?_, rfl⟩
    have hadj := adjacent_act Γ actor⁻¹ ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
    have hfix : Γ.act actor⁻¹ vertex = vertex :=
      (Set.ext_iff.mp (Γ.stabilizer_def vertex) actor⁻¹).mp
        ((GAt Γ vertex).inv_mem hactor)
    rw [hfix] at hadj
    exact (mem_neighborhood_iff_adjacent Γ).mpr hadj
  exact hmap ⟨element, helement, rfl⟩

public theorem nine_seven_neighbor_module_le_neighborhood
    (Γ : CosetGraphContext G T A B) {vertex neighbor : Γ.Vertex}
    (hadj : Γ.adjacent vertex neighbor) :
    VAt Γ neighbor ≤ GeneratedNeighborhoodV Γ vertex := by
  exact le_sSup ⟨neighbor, (mem_neighborhood_iff_adjacent Γ).mpr hadj, rfl⟩

public theorem nine_seven_neighbor_join_le_own_core
    (ctx : SectionNineLocalContext G T A B) (hb : 3 < ctx.criticalPath.length)
    (vertex : ctx.Γ.Vertex) :
    sSup {subgroup : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood ctx.Γ vertex ∧
      subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} ≤ QAt ctx.Γ vertex := by
  apply sSup_le
  rintro subgroup ⟨first, hfirst, rfl⟩
  rw [GeneratedNeighborhoodV]
  apply sSup_le
  rintro subgroup ⟨second, hsecond, rfl⟩
  rw [ctx.Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨third, hthird, rfl⟩
  have hfirstAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hfirst
  have hsecondAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hsecond
  have hthirdAdj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hthird
  have hdist := ctx.Γ.distance_le_of_path 3 ![third, second, first, vertex] (by
    intro step
    fin_cases step
    · exact ctx.Γ.adjacent_symm hthirdAdj
    · exact ctx.Γ.adjacent_symm hsecondAdj
    · exact ctx.Γ.adjacent_symm hfirstAdj)
  exact critical_minimality ctx.Γ ctx.criticalPath (hdist.trans_lt hb)

public theorem nine_seven_initial_normality_obstructions
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hstartCard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    let initialJoin := sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor}
    (∀ neighbor, neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a →
      (¬ GAt ctx.Γ ctx.criticalPath.a ≤
        Subgroup.normalizer (VAt ctx.Γ neighbor : Set G)) ∧
      (¬ GAt ctx.Γ ctx.criticalPath.a ≤
        Subgroup.normalizer (GeneratedNeighborhoodV ctx.Γ neighbor : Set G))) ∧
    (¬ GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a : Set G)) ∧
    (¬ GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.normalizer (initialJoin : Set G)) := by
  let initialJoin := sSup {subgroup : Subgroup G | ∃ neighbor,
    neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      subgroup = GeneratedNeighborhoodV ctx.Γ neighbor}
  have hne : ZAt ctx.Γ ctx.criticalPath.a ≠ ⊥ := by
    intro hbot
    simp [hbot] at hstartCard
  have hjoin := (nine_seven_center_join ctx ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one ctx.criticalPath.a⟩).1
  have hmodule : VAt ctx.Γ ctx.criticalPath.a ≠ ⊥ := by
    rwa [← hjoin]
  have hlocal : 3 < ctx.toLocalContext.criticalPath.length := hb
  have hWne (neighbor : ctx.Γ.Vertex)
      (hadj : ctx.Γ.adjacent ctx.criticalPath.a neighbor) :
      GeneratedNeighborhoodV ctx.Γ neighbor ≠ ⊥ := by
    intro hbot
    apply hmodule
    exact le_bot_iff.mp (hbot ▸ nine_seven_neighbor_module_le_neighborhood ctx.Γ
      (ctx.Γ.adjacent_symm hadj))
  refine ⟨?_, ?_, ?_⟩
  · intro neighbor hneighbor
    have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
    refine ⟨nine_seven_module_not_normalized_by_neighbor ctx.toLocalContext
      (by omega) (ctx.Γ.adjacent_symm hadj) ?_,
      nine_seven_neighborhood_not_normalized_by_neighbor ctx.toLocalContext
        (by omega) (ctx.Γ.adjacent_symm hadj) (hWne neighbor hadj)⟩
    intro hbot
    apply hne
    exact le_bot_iff.mp (hbot ▸ nine_seven_neighbor_center_le_module ctx.Γ
      (ctx.Γ.adjacent_symm hadj))
  · apply nine_seven_neighborhood_not_normalized_by_neighbor ctx.toLocalContext
      (by omega) ctx.criticalPath.firstStep_adj
    intro hbot
    apply hne
    have hle := (nine_seven_neighbor_center_le_module ctx.Γ
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)).trans
        (nine_seven_neighbor_module_le_neighborhood ctx.Γ ctx.criticalPath.firstStep_adj)
    exact le_bot_iff.mp (hbot ▸ hle)
  · intro hnormal
    have hUne : initialJoin ≠ ⊥ := by
      intro hbot
      apply hWne ctx.criticalPath.firstStep ctx.criticalPath.firstStep_adj
      have hle : GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.firstStep ≤ initialJoin :=
        le_sSup ⟨ctx.criticalPath.firstStep,
          (mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj, rfl⟩
      exact le_bot_iff.mp (hbot ▸ hle)
    apply hUne
    exact nine_seven_edge_invariant_two_subgroup_eq_bot ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep_adj initialJoin
      (nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ ctx.criticalPath.a initialJoin
        (nine_seven_neighbor_join_le_own_core ctx.toLocalContext hb ctx.criticalPath.a))
      (nine_seven_stabilizer_normalizes_neighbor_join ctx.Γ ctx.criticalPath.a) hnormal

end Stellmacher.SectionNine
