module

public import Stellmacher.SectionEight.GeneratedEightFiveCriticalCenters
public import Stellmacher.SectionEight.GeneratedEightFiveCriticalCore
public import Stellmacher.SectionEight.GeneratedEightFiveBackwardTransport

/-! # Generated critical distance two after the order-four recognition

This is the full second paragraph of (8.5), printed pp.40–41 of
`refs/files/stellmacher-n-group.pdf`. The graph remains on the join, and
Hypothesis Two remains on H. Genuine local critical-center and backward
transport kernels are combined with core control derived from the ambient
Sylow and subnormal residual. No (8.5) or (8.6) is assumed.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

private theorem eight_five_length_lower_bound
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcomm : ⁅z graph path.a, z graph path.a'⁆ ≠ ⊥)
    (hcenter : z graph path.firstStep ≤
      CenterAmbient (stabilizer graph path.firstStep)) :
    2 ≤ path.length := by
  by_contra hlength
  have hone : path.length = 1 := by have := path.length_pos; omega
  have hfirst : path.firstStep = path.a' := by
    calc
      path.firstStep = path.path ⟨1, by omega⟩ := path.path_first.symm
      _ = path.path ⟨path.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hone.symm
      _ = path.a' := path.path_end
  rw [hfirst] at hcenter
  have hcontain := (lemma_seven_four hyp graph path).first_containment
  apply hcomm
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  exact hcenter.trans ((SevenSix.centerAmbient_le_centralizer _).trans
    (Subgroup.centralizer_le (hcontain.1.trans hcontain.2)))

private theorem eight_five_second_neighbor_module_le_penultimate_core
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 2 < path.length)
    (vertex : graph.Vertex)
    (hvertex : vertex ∈ neighborhood graph (path.path ⟨2, by omega⟩)) :
    v graph vertex ≤ q graph (path.path ⟨path.length - 1, by omega⟩) := by
  rw [v, graph.vAt_def]
  apply sSup_le
  rintro center ⟨neighbor, hneighbor, rfl⟩
  change z graph neighbor ≤ _
  apply SevenSix.critical_minimality graph path
  let route : Fin (path.length - 1 + 1) → graph.Vertex := fun index =>
    if index.val = 0 then neighbor else
      if index.val = 1 then vertex else path.path ⟨index.val, by omega⟩
  have hstart : route 0 = neighbor := by simp [route]
  have hend : route ⟨path.length - 1, Nat.lt_succ_self _⟩ =
      path.path ⟨path.length - 1, by omega⟩ := by
    simp [route, show path.length - 1 ≠ 0 by omega,
      show path.length - 1 ≠ 1 by omega]
  have hadj : ∀ index : Fin (path.length - 1),
      graph.adjacent (route index.castSucc) (route index.succ) := by
    intro index
    change graph.adjacent
      (if index.val = 0 then neighbor else
        if index.val = 1 then vertex else path.path ⟨index.val, by omega⟩)
      (if index.val + 1 = 0 then neighbor else
        if index.val + 1 = 1 then vertex else path.path ⟨index.val + 1, by omega⟩)
    by_cases hzero : index.val = 0
    · have hstep := graph.adjacent_symm
        ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hneighbor)
      simpa [route, hzero] using hstep
    · by_cases hone : index.val = 1
      · have hstep := graph.adjacent_symm
          ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hvertex)
        simpa [route, hone] using hstep
      · have hstep := path.path_adj ⟨index.val, by omega⟩
        simpa [route, hzero, hone, show index.val + 1 ≠ 0 by omega,
          show index.val + 1 ≠ 1 by omega] using hstep
  have hdist := graph.distance_le_of_path (path.length - 1) route hadj
  rw [hstart, hend] at hdist
  exact hdist.trans_lt (by omega)

private theorem adjacent_stabilizers_generate
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (vertex : graph.Vertex) (hvertex : vertex ∈ neighborhood graph path.a) :
    stabilizer graph path.a ⊔ stabilizer graph vertex = ⊤ := by
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one hyp graph).local_transitivity path.a hfirst hvertex
  have hfix : graph.act (actor : G) path.a = path.a :=
    (Set.ext_iff.mp (graph.stabilizer_def path.a) _).mp actor.property
  have hbase : stabilizer graph path.a ⊔ stabilizer graph path.firstStep = ⊤ := by
    rcases path.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2, hyp.generated]
    · rw [hedge.1, hedge.2, sup_comm, hyp.generated]
  have hmap := congrArg
    (Subgroup.map (MulAut.conj (actor : G)⁻¹).toMonoidHom) hbase
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _
    (MulAut.conj (actor : G)⁻¹).surjective] at hmap
  change conjugateBy (stabilizer graph path.a) (actor : G)⁻¹ ⊔
    conjugateBy (stabilizer graph path.firstStep) (actor : G)⁻¹ = ⊤ at hmap
  rwa [← stabilizer_act, ← stabilizer_act, hfix, hactor] at hmap

private theorem eight_five_false_of_backward_commutator_bound
    {G : Type*} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : 1 < path.length)
    (hcomm : ⁅z graph path.a, z graph path.a'⁆ ≠ ⊥)
    (vertex : graph.Vertex) (hvertex : vertex ∈ neighborhood graph path.a)
    (hgenerate : (stabilizer graph path.a ⊓ stabilizer graph vertex) ⊔
      z graph path.a' = stabilizer graph path.a)
    (hbound : ⁅z graph path.a', v graph vertex⁆ ≤ z graph path.a) : False := by
  have hreverse : path.a ∈ neighborhood graph vertex :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
      (graph.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent graph).mp hvertex))
  have hcenter : z graph path.a ≤ v graph vertex := by
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a, hreverse, rfl⟩
  have hterminal : z graph path.a' ≤ Subgroup.normalizer (v graph vertex : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (hbound.trans hcenter)
  have hinitial : stabilizer graph path.a ≤
      Subgroup.normalizer (v graph vertex : Set G) := by
    rw [← hgenerate]
    exact sup_le (inf_le_right.trans (stabilizer_le_normalizer_v graph vertex)) hterminal
  have hnormal : (v graph vertex).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← adjacent_stabilizers_generate hyp graph path vertex hvertex]
    exact sup_le hinitial (stabilizer_le_normalizer_v graph vertex)
  have hcore : v graph vertex ≤ q graph vertex := by
    rw [v, graph.vAt_def]
    apply sSup_le
    rintro center ⟨neighbor, hneighbor, rfl⟩
    apply SevenSix.critical_minimality graph path
    have hdist : graph.distance neighbor vertex = 1 := by
      exact Set.ext_iff.mp (graph.neighbors_def vertex) neighbor |>.mp hneighbor
    omega
  have htwoCore : IsPGroup 2 (q graph vertex) := by
    rw [q, graph.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer graph vertex)).map _
  have htwo : IsPGroup 2 (v graph vertex) :=
    htwoCore.of_injective (Subgroup.inclusion hcore) (Subgroup.inclusion_injective hcore)
  have hbot : v graph vertex = ⊥ := by
    apply bot_unique
    have hle : v graph vertex ≤ pCore 2 G := le_sSup ⟨hnormal, htwo⟩
    rwa [hyp.twoCore_eq_bot] at hle
  have hzbot : z graph path.a = ⊥ := bot_unique (hbot ▸ hcenter)
  apply hcomm
  rw [hzbot, Subgroup.commutator_bot_left]

/-- The distance conclusion of (8.5), after the order-four and quotient steps. -/
public theorem generated_eight_five_length_of_card_four_and_quotient
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two) :
    ctx.criticalPath.length = 2 := by
  have hyp := ctx.sectionSeven
  have hlower := eight_five_length_lower_bound hyp ctx.Γ ctx.criticalPath
    ctx.commutator_ne hcenter
  by_contra hne
  have hlength : 2 < ctx.criticalPath.length := by omega
  obtain ⟨hfirst, hlast⟩ := eight_five_critical_centers_of_card_four_and_quotient_local
    ctx.toLocalContext hcenter hfour hquotient hlength
  obtain ⟨hcoreFirst, hcoreLast⟩ := generated_eight_five_centralizer_core_control
    ctx hcenter hlength hfirst hlast
  obtain ⟨backward, transported, hbackward, _, htransported, hgenerate, hbound, hcomm⟩ :=
    eight_five_backward_transport_local ctx.toLocalContext hcenter hfour hquotient hlength hfirst hlast
  have htransportedCore := eight_five_second_neighbor_module_le_penultimate_core
    ctx.Γ ctx.criticalPath hlength transported htransported
  have hlastAdjacent : ctx.Γ.adjacent
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩)
      ctx.criticalPath.a' := by
    have hadj := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 1, by omega⟩
    have hindex : (⟨ctx.criticalPath.length - 1, by omega⟩ :
        Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rwa [hindex, ctx.criticalPath.path_end] at hadj
  have hlastNeighbor := (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr hlastAdjacent
  have hlastCoreTerminal :=
    ((lemma_seven_three hyp ctx.Γ).sylow_and_core _ _ hlastNeighbor default).2.2
  have hterminal : VAt ctx.Γ backward ≤ GAt ctx.Γ ctx.criticalPath.a' :=
    (hbound.trans (sup_le htransportedCore (hcoreFirst.trans hcoreLast))).trans
      hlastCoreTerminal
  exact eight_five_false_of_backward_commutator_bound hyp ctx.Γ ctx.criticalPath
    (by omega) ctx.commutator_ne backward hbackward hgenerate (hcomm hterminal)

end Stellmacher.SectionEight
