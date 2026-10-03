module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexModelSetup
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem conjugate_eq_of_same_left_coset
    {G : Type u} [Group G] (seed actors : Subgroup G)
    (cover : Subgroup actors)
    (hnormalize : cover.map actors.subtype ≤ Subgroup.normalizer (seed : Set G))
    (first second : actors)
    (hequal : (QuotientGroup.mk first : actors ⧸ cover) = QuotientGroup.mk second) :
    conjugateBy seed first = conjugateBy seed second := by
  have hrelative := QuotientGroup.eq.mp hequal
  have hnormal : (first : G)⁻¹ * (second : G) ∈ Subgroup.normalizer (seed : Set G) :=
    hnormalize (Subgroup.mem_map.mpr ⟨first⁻¹ * second, hrelative, rfl⟩)
  apply le_antisymm
  · rintro element ⟨representative, hrepresentative, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(second : G)⁻¹ * (first : G) * representative *
      ((second : G)⁻¹ * (first : G))⁻¹, ?_, ?_⟩
    · apply (Subgroup.mem_normalizer_iff.mp ?_ representative).mp hrepresentative
      simpa using (Subgroup.normalizer (seed : Set G)).inv_mem hnormal
    · change (second : G) * _ * (second : G)⁻¹ =
        (first : G) * representative * (first : G)⁻¹
      group
  · rintro element ⟨representative, hrepresentative, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(first : G)⁻¹ * (second : G) * representative *
      ((first : G)⁻¹ * (second : G))⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hnormal representative).mp hrepresentative
    · change (first : G) * _ * (first : G)⁻¹ =
        (second : G) * representative * (second : G)⁻¹
      group

public theorem eight_six_three_conjugates_of_index_three
    {G : Type u} [Group G] [Finite G] (seed actors : Subgroup G)
    (cover : Subgroup actors)
    (hnormalize : cover.map actors.subtype ≤ Subgroup.normalizer (seed : Set G))
    (hindex : cover.index = 3) :
    ∃ first second third : actors, ∀ actor : actors,
      conjugateBy seed actor = conjugateBy seed first ∨
      conjugateBy seed actor = conjugateBy seed second ∨
      conjugateBy seed actor = conjugateBy seed third := by
  classical
  let _ := Fintype.ofFinite (actors ⧸ cover)
  let enumeration : (actors ⧸ cover) ≃ Fin 3 :=
    Fintype.equivFinOfCardEq (by simpa [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
      using hindex)
  let representative (index : Fin 3) : actors := (enumeration.symm index).out
  refine ⟨representative 0, representative 1, representative 2, ?_⟩
  intro actor
  have hsame : conjugateBy seed actor =
      conjugateBy seed (representative (enumeration (QuotientGroup.mk actor))) := by
    apply conjugate_eq_of_same_left_coset seed actors cover hnormalize
    simp [representative]
  have hcases : enumeration (QuotientGroup.mk actor) = 0 ∨
      enumeration (QuotientGroup.mk actor) = 1 ∨
      enumeration (QuotientGroup.mk actor) = 2 := by omega
  rcases hcases with hequal | hequal | hequal
  · exact Or.inl (hequal ▸ hsame)
  · exact Or.inr (Or.inl (hequal ▸ hsame))
  · exact Or.inr (Or.inr (hequal ▸ hsame))

public theorem eight_six_sylow_index_three_of_quotient
    {G : Type u} [Group G] [Finite G] (actors core : Subgroup G)
    (sylow : Sylow 2 actors)
    (hcore : core.subgroupOf actors ≤ sylow)
    (hquotient : QuotientIsModel actors core SL2Two) :
    (sylow : Subgroup actors).index = 3 := by
  obtain ⟨projection, hsurjective, hkernel⟩ := hquotient
  let imageSylow := sylow.mapSurjective hsurjective
  have himageCard : Nat.card imageSylow = 2 := by
    rw [imageSylow.card_eq_multiplicity]
    have hmodelCard : Nat.card SL2Two = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hmodelCard]
    change 2 ^ (Nat.factorization (3 * 2)) 2 = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hproduct := (imageSylow : Subgroup SL2Two).index_mul_card
  have hmodelCard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  rw [himageCard, hmodelCard] at hproduct
  have hindex : (imageSylow : Subgroup SL2Two).index = 3 := by omega
  have hkernelLe : projection.ker ≤ sylow := hkernel ▸ hcore
  exact ((sylow : Subgroup actors).index_map_eq hsurjective hkernelLe).symm.trans
    hindex

public theorem eight_six_neighbor_join_eq_conjugate_closure
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (vertex neighbor : graph.Vertex)
    (hadj : neighbor ∈ neighborhood graph vertex) :
    VAt graph vertex = conjugateClosure (ZAt graph neighbor) (GAt graph vertex) := by
  have hseed : z graph neighbor ≤ v graph vertex := by
    rw [v, graph.vAt_def]
    exact le_sSup ⟨neighbor, hadj, rfl⟩
  apply le_antisymm
  · change v graph vertex ≤ _
    rw [v, graph.vAt_def]
    apply sSup_le
    rintro subgroup ⟨other, hother, rfl⟩
    obtain ⟨actor, hactor⟩ := (lemma_seven_one hyp graph).local_transitivity vertex hadj hother
    change z graph other ≤ _
    rw [← hactor, z_act]
    rintro element ⟨representative, hrepresentative, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨actor⁻¹, ⟨representative, hrepresentative⟩, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro element ⟨actor, representative, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v graph vertex actor.property) representative).mp
      (hseed representative.property)

public theorem eight_six_common_line_le_conjugate
    {G : Type u} [Group G] (seed actors common : Subgroup G)
    (hcommon : common ≤ seed)
    (hnormal : actors ≤ Subgroup.normalizer (common : Set G)) (actor : actors) :
    common ≤ conjugateBy seed actor := by
  intro element helement
  refine Subgroup.mem_map.mpr ⟨(actor : G)⁻¹ * element * (actor : G), ?_, ?_⟩
  · apply hcommon
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hnormal (actors.inv_mem actor.property)) element).mp helement
  · change (actor : G) * _ * (actor : G)⁻¹ = element
    group

public theorem eight_six_next_three_conjugates_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ∃ first second third : GAt ctx.Γ ctx.criticalPath.firstStep,
      ∀ actor : GAt ctx.Γ ctx.criticalPath.firstStep,
        conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) actor =
          conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) first ∨
        conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) actor =
          conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) second ∨
        conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) actor =
          conjugateBy (ZAt ctx.Γ ctx.criticalPath.a) third := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let actors := GAt graph path.firstStep
  obtain ⟨hsylowLe, sylow, hsylow⟩ :=
    (SevenSix.edge_sylow_data ctx.sectionSeven graph path).2
  have hcoreLe : QAt graph path.firstStep ≤ actors := by
    change graph.twoCoreAt path.firstStep ≤ graph.vertexStabilizer path.firstStep
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hnative : (QAt graph path.firstStep).subgroupOf actors ≤ sylow := by
    apply (Subgroup.map_le_map_iff_of_injective actors.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hcoreLe, hsylow]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven graph path).2
  have hindex := eight_six_sylow_index_three_of_quotient actors _ sylow hnative hquotient
  apply eight_six_three_conjugates_of_index_three _ actors sylow ?_ hindex
  rw [hsylow]
  exact (SevenSix.edge_sylow_data ctx.sectionSeven graph path).1.1.trans
    (stabilizer_le_normalizer_z graph path.a)

public theorem eight_six_next_v_card_le_of_quotient_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcommutator : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) ≤ 16 := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  obtain ⟨hlineCard, hlineLe⟩ := eight_six_first_step_fixed_line_local ctx hcenter hcard
  change path.length = 2 at hlength
  have hback : path.a ∈ neighborhood graph path.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm path.firstStep_adj)
  have hclosure := eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven
    graph path.firstStep path.a hback
  obtain ⟨first, second, third, henumeration⟩ := eight_six_next_three_conjugates_local
    ctx hquotient
  have hcommon (actor : GAt graph path.firstStep) :
      ZAt graph path.firstStep ≤ conjugateBy (ZAt graph path.a) actor :=
    eight_six_common_line_le_conjugate _ _ _ hlineLe
      (stabilizer_le_normalizer_z graph path.firstStep) actor
  have hderived : ⁅VAt graph path.firstStep, VAt graph path.firstStep⁆ ≤
      ZAt graph path.firstStep := by
    rw [← hcommutator]
    exact Subgroup.commutator_mono le_rfl
      (SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) path.firstStep)
  rw [hclosure] at hderived ⊢
  exact eight_six_three_conjugates_card_le _ _ _ first second third hcard hlineCard
    (hcommon first) (hcommon second) (hcommon third) henumeration hderived

end Stellmacher.SectionEight
