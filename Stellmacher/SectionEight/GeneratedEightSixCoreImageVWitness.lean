module

public import Stellmacher.SectionEight.GeneratedEightSixNeighborGeneration

/-!
# Cubic V-witness for the opposite-core intersection

Source: Stellmacher, printed p.41, equation (1). Length two and the
critical commutator force each neighboring module to act nontrivially
on the cubic neighborhood. Two punctured-neighborhood swaps transport
the normal intersection to the remaining pair of neighboring cores.
The witness is inverted to match the graph's right-action convention.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_core_image_v_actor_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hnormal : NormalIn D (GAt ctx.Γ ctx.criticalPath.a)) :
    ∃ actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ previous ⊓
        (QAt ctx.Γ previous).map (MulAut.conj actor).toMonoidHom ≤ D := by
  classical
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hprevious : graph.adjacent path.a previous :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mp hprev.1
  have hterminalNeighbor : path.a' ∈ neighborhood graph path.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hstep := path.path_adj ⟨1, by omega⟩
    have hlast : (⟨1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hlast, path.path_end] at hstep
    simpa only [Fin.castSucc_mk, path.path_first] using hstep
  have hterminalV : z graph path.a' ≤ v graph path.firstStep := by
    rw [v, graph.vAt_def]
    exact le_sSup ⟨path.a', hterminalNeighbor, rfl⟩
  have hnot : ¬ v graph path.firstStep ≤ q graph path.a := by
    intro hle
    have hcentral : z graph path.a ≤ Subgroup.centralizer (q graph path.a : Set G) :=
      ((lemma_seven_three ctx.sectionSeven graph).center_core path.a path.firstStep hfirst).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
    exact ctx.commutator_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.centralizer_le (hterminalV.trans hle))))
  have hpreviousNot : ¬ v graph previous ≤ q graph path.a := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven graph).local_transitivity
      path.a hfirst hprev.1
    have hfix : graph.act (actor : G) path.a = path.a :=
      (Set.ext_iff.mp (graph.stabilizer_def path.a) actor).mp actor.property
    intro hle
    apply hnot
    have hmapCore : (q graph path.a).map
        (MulAut.conj (actor : G)⁻¹).toMonoidHom = q graph path.a := by
      rw [← SevenSix.q_act, hfix]
    rw [← hactor, v_act, ← hmapCore] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (actor : G)⁻¹).injective).mp hle
  have hVcore (neighbor : graph.Vertex) : v graph neighbor ≤ q graph neighbor :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) neighbor
  have hVedge (neighbor : graph.Vertex) (hadj : neighbor ∈ neighborhood graph path.a) :
      v graph neighbor ≤ GAt graph path.a ⊓ GAt graph neighbor := by
    apply (hVcore neighbor).trans
    refine le_inf (eight_six_generation_neighbor_core_le ctx.sectionSeven
      graph path neighbor hadj).2 ?_
    rw [q, graph.twoCoreAt_def]
    exact SevenSix.twoCoreIn_le _
  have hlocal := SectionNine.cubic_local_action_of_sl2Two_quotient
    graph ctx.sectionSeven path.a hquot
  let Points := {neighbor // graph.adjacent path.a neighbor}
  let : Finite graph.Vertex := graph.finiteVertex
  let := Fintype.ofFinite Points
  obtain ⟨third, hthird⟩ : ∃ third : Points,
      third ∉ ({⟨path.firstStep, path.firstStep_adj⟩, ⟨previous, hprevious⟩} : Finset Points) := by
    have hcard : ({⟨path.firstStep, path.firstStep_adj⟩, ⟨previous, hprevious⟩} :
        Finset Points).card < (Finset.univ : Finset Points).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hlocal.degree]
      exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp)
    obtain ⟨third, _, hthird⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨third, hthird⟩
  have hthirdFirst : (third : graph.Vertex) ≠ path.firstStep := by
    intro heq
    exact hthird (Finset.mem_insert.mpr (Or.inl (Subtype.ext heq)))
  have hthirdPrevious : (third : graph.Vertex) ≠ previous := by
    intro heq
    exact hthird (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext heq))))
  have hthirdNeighbor : (third : graph.Vertex) ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr third.property
  obtain ⟨actor, hactor⟩ := hlocal.punctured_transitivity path.firstStep path.firstStep_adj
    (v graph path.firstStep) (hVedge _ hfirst) hnot
    ⟨hprev.1, hprev.2⟩ ⟨hthirdNeighbor, hthirdFirst⟩
  obtain ⟨transport, htransport⟩ := hlocal.punctured_transitivity previous hprevious
    (v graph previous) (hVedge _ hprev.1) hpreviousNot
    ⟨hfirst, hprev.2.symm⟩ ⟨hthirdNeighbor, hthirdPrevious⟩
  have hfix : graph.act (transport : G) previous = previous :=
    (Set.ext_iff.mp (graph.stabilizer_def previous) transport).mp
      ((hVedge _ hprev.1) transport.property).2
  have hnormalizer : GAt graph path.a ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
  have hDmap : D.map (MulAut.conj (transport : G)⁻¹).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem
        (hnormalizer ((hVedge _ hprev.1) transport.property).1))
  have hintersection : QAt graph previous ⊓ QAt graph third = D := by
    rw [hD, Subgroup.map_inf _ _ _ (MulAut.conj (transport : G)⁻¹).injective,
      ← SevenSix.q_act, ← SevenSix.q_act, hfix, htransport] at hDmap
    exact hDmap.trans hD.symm
  refine ⟨(actor : G)⁻¹, (VAt graph path.firstStep).inv_mem
    actor.property, ?_⟩
  have hmap : (QAt graph previous).map (MulAut.conj (actor : G)⁻¹).toMonoidHom =
      QAt graph third := by
    rw [← SevenSix.q_act, hactor]
  change QAt graph previous ⊓
    (QAt graph previous).map (MulAut.conj (actor : G)⁻¹).toMonoidHom ≤ D
  rw [hmap, hintersection]

end Stellmacher.SectionEight
