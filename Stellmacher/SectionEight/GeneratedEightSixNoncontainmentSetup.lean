module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionEight.GeneratedEightThree
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.ResidualCommutatorIdempotence

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_neighbor_intersection_le_of_previous_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous neighbor : graph.Vertex) (D : Subgroup G)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (hneighbor : neighbor ∈ Later.Neighborhood graph path.a)
    (hnormal : NormalIn D (GAt graph path.a))
    (hcontained : VAt graph previous ⊓ QAt graph path.a ≤ D) :
    VAt graph neighbor ⊓ QAt graph path.a ≤ D := by
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hprevious hneighbor
  have hDN : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
  have hDmap : D.map (MulAut.conj (actor : G)⁻¹).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem (hDN actor.property))
  have hQmap : (QAt graph path.a).map (MulAut.conj (actor : G)⁻¹).toMonoidHom =
      QAt graph path.a :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (QAt graph path.a : Set G)).inv_mem
        (SevenSix.stabilizer_le_normalizer_q graph path.a actor.property))
  have hmap := Subgroup.map_mono
    (f := (MulAut.conj (actor : G)⁻¹).toMonoidHom) hcontained
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective,
    hDmap, hQmap] at hmap
  rw [← hactor]
  change v graph (graph.act actor previous) ⊓ QAt graph path.a ≤ D
  rwa [v_act]

public theorem eight_six_core_eq_intersection_of_previous_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hprevious : previous ∈ Later.Neighborhood graph path.a)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hcontained : VAt graph previous ⊓ QAt graph path.a ≤ D) : Q = D := by
  have hfirst := eight_six_neighbor_intersection_le_of_previous_le hyp graph path
    previous path.firstStep D hprevious
    ((SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj)
    data.intersection_normal hcontained
  rw [data.core_generation]
  exact sup_eq_right.mpr (sup_le hcontained hfirst)

public theorem eight_six_initial_core_eq_center_of_residual_core_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hresidual : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      ZAt ctx.Γ ctx.criticalPath.a) :
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a := by
  apply eight_three_core_eq_center_local ctx hcenter
  have hbound := SevenSix.residual_commutator_core_le
    (GAt ctx.Γ ctx.criticalPath.a)
  have hE : EAt ctx.Γ ctx.criticalPath.a =
      twoResidualIn (GAt ctx.Γ ctx.criticalPath.a) := ctx.Γ.twoResidualAt_def _
  have hQ : QAt ctx.Γ ctx.criticalPath.a =
      twoCoreIn (GAt ctx.Γ ctx.criticalPath.a) := ctx.Γ.twoCoreAt_def _
  rw [← hE, ← hQ] at hbound
  rw [Subgroup.commutator_comm]
  exact hbound.trans hresidual

public theorem eight_six_initial_commutator_le_of_core_eq_intersection
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData graph path previous D L Q)
    (hQ : Q = twoCoreIn L) (hQD : Q = D)
    (hcomm : ⁅D, L⁆ = ZAt graph path.a) :
    ⁅QAt graph path.a, EAt graph path.a⁆ ≤ ZAt graph path.a := by
  have hcorep : IsPGroup 2 (QAt graph path.a) := by
    change IsPGroup 2 (graph.twoCoreAt path.a)
    rw [graph.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  have hnormal : ((QAt graph path.a).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (data.closure_le.trans (SevenSix.stabilizer_le_normalizer_q graph path.a))
  have hlocalp : IsPGroup 2 ((QAt graph path.a).subgroupOf L) :=
    hcorep.comap_of_injective L.subtype L.subtype_injective
  have hlocalcore : (QAt graph path.a).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨hnormal, hlocalp⟩
  have hE : EAt graph path.a = twoResidualIn (GAt graph path.a) :=
    graph.twoResidualAt_def _
  have hcore : QAt graph path.a = twoCoreIn (GAt graph path.a) :=
    graph.twoCoreAt_def _
  have hbound : ⁅QAt graph path.a, EAt graph path.a⁆ ≤
      EAt graph path.a ⊓ QAt graph path.a := by
    rw [hE, hcore, Subgroup.commutator_comm]
    exact (SevenSix.residual_commutator_core_le _).trans_eq
      (SevenSix.residual_core_eq_inter_core _)
  have hcommD : ⁅QAt graph path.a, EAt graph path.a⁆ ≤ D := by
    rw [← hQD, hQ]
    intro element helement
    have hmem := hbound helement
    exact Subgroup.mem_map.mpr
      ⟨⟨element, data.residual_le hmem.1⟩, hlocalcore hmem.2, rfl⟩
  have hidempotent :
      ⁅⁅QAt graph path.a, EAt graph path.a⁆, EAt graph path.a⁆ =
        ⁅QAt graph path.a, EAt graph path.a⁆ := by
    rw [hE]
    exact commutator_twoResidualAmbient_idempotent _ _ hcorep
      (SevenSix.stabilizer_le_normalizer_q graph path.a)
  rw [← hidempotent]
  exact (Subgroup.commutator_mono hcommD data.residual_le).trans_eq hcomm

public theorem generated_eight_six_initial_core_ne_center
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : 1 < ctx.criticalPath.length) :
    QAt ctx.Γ ctx.criticalPath.a ≠ ZAt ctx.Γ ctx.criticalPath.a := by
  intro heq
  apply generated_lemma_eight_three ctx hcenter
  have hshort : ZAt ctx.Γ ctx.criticalPath.a ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
    apply SevenSix.critical_minimality ctx.Γ ctx.criticalPath
    rw [(SevenSix.adjacent_iff_distance_eq_one ctx.Γ).mp ctx.criticalPath.firstStep_adj]
    exact hlength
  have hcore : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.a := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.a
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def,
      SevenSix.residual_core_eq_inter_core]
    exact inf_le_right
  exact hcore.trans (heq.le.trans hshort)

public theorem generated_eight_six_predecessor_intersection_not_le_of_equation_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprevious : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (hQ : Q = twoCoreIn L)
    (hcomm : ⁅D, L⁆ = ZAt ctx.Γ ctx.criticalPath.a) :
    ¬ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ D := by
  intro hcontained
  have hQD := eight_six_core_eq_intersection_of_previous_le ctx.sectionSeven
    ctx.Γ ctx.criticalPath previous D L Q hprevious data hcontained
  have hbound := eight_six_initial_commutator_le_of_core_eq_intersection
    ctx.Γ ctx.criticalPath previous D L Q data hQ hQD hcomm
  exact generated_eight_six_initial_core_ne_center ctx hcenter (by omega)
    (eight_three_core_eq_center_local ctx.toLocalContext hcenter hbound)

end Stellmacher.SectionEight
