module

public import Stellmacher.SectionEight.GeneratedEightSixNextSmallStructure

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_nonabelian_plane_normalizer_index_three
    {G : Type u} [Group G] [Finite G] (seed actors : Subgroup G)
    [IsMulCommutative seed] (cover : Subgroup actors)
    (hnormalize : cover.map actors.subtype ≤ Subgroup.normalizer (seed : Set G))
    (hindex : cover.index = 3)
    (hnoncommutative : ⁅conjugateClosure seed actors,
      conjugateClosure seed actors⁆ ≠ ⊥) :
    ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3 := by
  have hle : cover ≤ (Subgroup.normalizer (seed : Set G)).subgroupOf actors := by
    intro actor hactor
    exact hnormalize (Subgroup.mem_map.mpr ⟨actor, hactor, rfl⟩)
  have hdiv := Subgroup.index_dvd_of_le hle
  rw [hindex] at hdiv
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
  · have htop := Subgroup.index_eq_one.mp hone
    have hnormal : actors ≤ Subgroup.normalizer (seed : Set G) := by
      intro actor hactor
      have hmem : (⟨actor, hactor⟩ : actors) ∈
          (Subgroup.normalizer (seed : Set G)).subgroupOf actors := by
        rw [htop]
        trivial
      exact hmem
    have hclosure : conjugateClosure seed actors ≤ seed := by
      apply (Subgroup.closure_le _).mpr
      rintro element ⟨actor, representative, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hnormal actor.property)
        representative).mp representative.property
    have hcommutative : ⁅seed, seed⁆ = ⊥ :=
      Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
    exact False.elim (hnoncommutative (le_bot_iff.mp
      ((Subgroup.commutator_mono hclosure hclosure).trans hcommutative.le)))
  · exact hthree

public theorem eight_six_next_v_intersection_eq_plane_centralizer_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) := by
  have hle : VAt ctx.Γ ctx.criticalPath.firstStep ≤ S :=
    (SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
      (by omega) ctx.criticalPath.firstStep).trans
      (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hedge : S ⊓ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) =
      QAt ctx.Γ ctx.criticalPath.a :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).edge_centralizer
  rw [← hedge,
    ← inf_assoc, inf_eq_left.mpr hle]

public theorem eight_six_next_v_plane_recognition_inputs_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcommutator : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hnext : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let seed := ZAt ctx.Γ ctx.criticalPath.a
    let actors := GAt ctx.Γ ctx.criticalPath.firstStep
    let common := ZAt ctx.Γ ctx.criticalPath.firstStep
    let whole := VAt ctx.Γ ctx.criticalPath.firstStep
    seed ≤ actors ∧ IsElementaryAbelian 2 seed ∧
      Nat.card seed = 4 ∧ Nat.card common = 2 ∧ common ≤ seed ∧
      actors ≤ Subgroup.centralizer (common : Set G) ∧
      whole = conjugateClosure seed actors ∧ ⁅whole, whole⁆ = common ∧
      ((Subgroup.normalizer (seed : Set G)).subgroupOf actors).index = 3 := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  change path.length = 2 at hlength
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hback : path.a ∈ neighborhood graph path.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj)
  have hseedS : ZAt graph path.a ≤ S :=
    ((lemma_seven_four ctx.sectionSeven graph path).first_containment.1.trans
      (SevenSix.neighbor_join_le_core_of_length_gt_one graph path
        (by omega) path.firstStep)).trans
      (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2
  have hedge := SevenSix.edge_sylow_data ctx.sectionSeven graph path
  have hseedActors : ZAt graph path.a ≤ GAt graph path.firstStep :=
    hseedS.trans hedge.2.1
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hcentral : GAt graph path.firstStep ≤
      Subgroup.centralizer (ZAt graph path.firstStep : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  refine ⟨hseedActors,
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven graph hfirst,
    hcard, hline.1, hline.2, hcentral,
    eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven graph
      path.firstStep path.a hback,
    eight_six_next_v_derived_eq_line_local ctx hcenter hlength hcard hcommutator, ?_⟩
  obtain ⟨_, sylow, hsylow⟩ := hedge.2
  have hcoreActors : QAt graph path.firstStep ≤ GAt graph path.firstStep := by
    change graph.twoCoreAt path.firstStep ≤ graph.vertexStabilizer path.firstStep
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hcoreSylow : (QAt graph path.firstStep).subgroupOf
      (GAt graph path.firstStep) ≤ sylow := by
    apply (Subgroup.map_le_map_iff_of_injective
      (GAt graph path.firstStep).subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hcoreActors, hsylow]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven graph hfirst
  refine eight_six_nonabelian_plane_normalizer_index_three
    (ZAt graph path.a) (GAt graph path.firstStep) sylow
    ?_ (eight_six_sylow_index_three_of_quotient _ _ sylow hcoreSylow hnext) ?_
  · rw [hsylow]
    exact hedge.1.1.trans (stabilizer_le_normalizer_z graph path.a)
  · rw [← eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven graph
      path.firstStep path.a hback]
    exact eight_six_next_v_noncommutative_local ctx hlength

end Stellmacher.SectionEight
