module

public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionNine.CubicLocalAction

/-!
# Normality of the opposite core intersection in (8.6)

At critical distance two, the first neighbor-center join crosses the initial
core. Its commutator with its own core is the central order-two line inside
the initial center. Local transitivity transports both facts to any neighbor
of the initial vertex. Consequently both selected neighbor-center joins
normalize the intersection of the two selected cores: their commutators
with that intersection lie in the initial center, contained in both cores.
The initial core also normalizes the intersection.

The actual initial SL₂(2) quotient supplies a cubic local action and edge
indices two and three. The first join supplements the initial core in its
edge stabilizer. The other join cannot lie in that edge stabilizer: it would
fix two of the three neighbors and hence lie in the initial core. Thus the
edge stabilizer and the other join generate the initial stabilizer, proving
normality of the actual intersection, not its normal closure.

Source: Stellmacher, printed p.41, paragraph preceding (8.6)(1),
`refs/files/stellmacher-n-group.pdf`. The generated adapter retains Hypothesis
Two on the ambient group and uses the graph-preserving local context.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem core_le_self
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (vertex : Γ.Vertex) :
    QAt Γ vertex ≤ GAt Γ vertex := by
  rw [QAt, q, Γ.twoCoreAt_def]
  exact SevenSix.twoCoreIn_le _

private theorem core_le_neighbor
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) {vertex neighbor : Γ.Vertex}
    (hadj : Γ.adjacent vertex neighbor) : QAt Γ vertex ≤ GAt Γ neighbor :=
  ((lemma_seven_three hyp Γ).sylow_and_core vertex neighbor
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj) default).2.2

private theorem sup_eq_of_prime_relIndex
    {G : Type u} [Group G] (small extra container : Subgroup G)
    (hsmall : small ≤ container) (hextra : extra ≤ container)
    {prime : ℕ} (hprime : Nat.Prime prime)
    (hindex : small.relIndex container = prime) (hout : ¬ extra ≤ small) :
    small ⊔ extra = container := by
  have htower := Subgroup.relIndex_mul_relIndex small (small ⊔ extra) container
    le_sup_left (sup_le hsmall hextra)
  rw [hindex] at htower
  have hdiv : small.relIndex (small ⊔ extra) ∣ prime := ⟨_, htower.symm⟩
  rcases hprime.eq_one_or_self_of_dvd _ hdiv with hone | hfull
  · exact (hout (le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone))).elim
  · rw [hfull] at htower
    have hone : (small ⊔ extra).relIndex container = 1 := by
      nlinarith [hprime.pos]
    exact le_antisymm (sup_le hsmall hextra) (Subgroup.relIndex_eq_one.mp hone)

private theorem cubic_fix_two
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (middle left right : Γ.Vertex)
    (hmodel : QuotientIsModel (GAt Γ middle) (QAt Γ middle) SL2Two)
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hne : left ≠ right) :
    GAt Γ middle ⊓ GAt Γ left ⊓ GAt Γ right ≤ QAt Γ middle := by
  intro actor hactor
  have hfixleft : Γ.act actor left = left :=
    (Set.ext_iff.mp (Γ.stabilizer_def left) actor).mp hactor.1.2
  have hfixright : Γ.act actor right = right :=
    (Set.ext_iff.mp (Γ.stabilizer_def right) actor).mp hactor.2
  have hfixmiddle : Γ.act actor middle = middle :=
    (Set.ext_iff.mp (Γ.stabilizer_def middle) actor).mp hactor.1.1
  have hlocal := SectionNine.cubic_local_action_of_sl2Two_quotient Γ hyp middle hmodel
  apply (hlocal.kernel ⟨actor, hactor.1.1⟩).mpr
  intro neighbor hneighbor
  by_cases hsame : neighbor = left
  · simpa only [hsame] using hfixleft
  by_cases hsameright : neighbor = right
  · simpa only [hsameright] using hfixright
  classical
  let Points := {vertex // Γ.adjacent middle vertex}
  let : Finite Γ.Vertex := Γ.finiteVertex
  let := Fintype.ofFinite Points
  have hcover : ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} :
      Finset Points) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hlocal.degree]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · intro heq
      exact hsameright (congrArg Subtype.val (Finset.mem_singleton.mp heq)).symm
    · intro hmem
      rcases Finset.mem_insert.mp hmem with heq | heq
      · exact hne (congrArg Subtype.val heq)
      · exact hsame (congrArg Subtype.val (Finset.mem_singleton.mp heq)).symm
  have hacted : Γ.adjacent middle (Γ.act actor neighbor) := by
    have htransport := adjacent_act Γ actor hneighbor
    rwa [hfixmiddle] at htransport
  have hmem : (⟨Γ.act actor neighbor, hacted⟩ : Points) ∈
      ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} : Finset Points) := by
    rw [hcover]
    exact Finset.mem_univ _
  have hinj : Function.Injective (Γ.act actor) := by
    intro first second heq
    have hinv := congrArg (Γ.act actor⁻¹) heq
    simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
  rcases hmem with heq | heq | heq
  · exact (hsame (hinj (heq.trans hfixleft.symm))).elim
  · exact (hsameright (hinj (heq.trans hfixright.symm))).elim
  · exact heq

private theorem cubic_edge_indices
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (middle neighbor : Γ.Vertex)
    (hadj : Γ.adjacent middle neighbor)
    (hmodel : QuotientIsModel (GAt Γ middle) (QAt Γ middle) SL2Two) :
    (QAt Γ middle).relIndex (GAt Γ middle ⊓ GAt Γ neighbor) = 2 ∧
      (GAt Γ middle ⊓ GAt Γ neighbor).relIndex (GAt Γ middle) = 3 := by
  have hedge := (SectionNine.cubic_local_action_of_sl2Two_quotient Γ hyp middle
    hmodel).edge_card neighbor hadj
  change Nat.card (GAt Γ middle ⊓ GAt Γ neighbor : Subgroup G) =
    2 * Nat.card (QAt Γ middle) at hedge
  have hcoreEdge := le_inf (core_le_self Γ middle) (core_le_neighbor hyp Γ hadj)
  have hfirst := ((QAt Γ middle).subgroupOf
    (GAt Γ middle ⊓ GAt Γ neighbor)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcoreEdge).toEquiv,
    hedge] at hfirst
  change (QAt Γ middle).relIndex (GAt Γ middle ⊓ GAt Γ neighbor) * _ = _ at hfirst
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hgroup := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (core_le_self Γ middle)).toEquiv,
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hgroup
  have hsecond := ((GAt Γ middle ⊓ GAt Γ neighbor).subgroupOf
    (GAt Γ middle)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show GAt Γ middle ⊓ GAt Γ neighbor ≤ GAt Γ middle from inf_le_left)).toEquiv,
    hedge] at hsecond
  change (GAt Γ middle ⊓ GAt Γ neighbor).relIndex (GAt Γ middle) * _ = _ at hsecond
  have hpos := Nat.card_pos (α := QAt Γ middle)
  constructor <;> nlinarith

public theorem eight_six_intersection_normal_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep) :
    NormalIn (QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a) := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  have hlength' : path.length = 2 := hlength
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hprevious : graph.adjacent path.a previous :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mp hprev.1
  have hline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hcomm := eight_six_first_commutator_local ctx hcenter hcard hlength
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
  have hneighborData (neighbor : graph.Vertex)
      (hneighbor : neighbor ∈ neighborhood graph path.a) :
      ⁅v graph neighbor, q graph neighbor⁆ = z graph neighbor ∧
        z graph neighbor ≤ z graph path.a ∧
          ¬ v graph neighbor ≤ q graph path.a := by
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven graph).local_transitivity
      path.a hfirst hneighbor
    have hfix : graph.act (actor : G) path.a = path.a :=
      (Set.ext_iff.mp (graph.stabilizer_def path.a) actor).mp actor.property
    have hmapComm := congrArg (fun subgroup : Subgroup G =>
      subgroup.map (MulAut.conj (actor : G)⁻¹).toMonoidHom) hcomm
    change (⁅v graph path.firstStep, q graph path.firstStep⁆).map _ =
      (z graph path.firstStep).map _ at hmapComm
    rw [Subgroup.map_commutator, ← v_act, ← SevenSix.q_act, ← z_act, hactor] at hmapComm
    have hmapLine := Subgroup.map_mono (f := (MulAut.conj (actor : G)⁻¹).toMonoidHom)
      hline.2
    change (z graph path.firstStep).map _ ≤ (z graph path.a).map _ at hmapLine
    rw [← z_act, ← z_act, hactor, hfix] at hmapLine
    refine ⟨hmapComm, hmapLine, ?_⟩
    intro hle
    apply hnot
    have hmapCore : (q graph path.a).map
        (MulAut.conj (actor : G)⁻¹).toMonoidHom = q graph path.a := by
      rw [← SevenSix.q_act, hfix]
    rw [← hactor, v_act, ← hmapCore] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj (actor : G)⁻¹).injective).mp hle
  have hVcore (neighbor : graph.Vertex) : v graph neighbor ≤ q graph neighbor :=
    SevenSix.neighbor_join_le_core_of_length_gt_one graph path (by omega) neighbor
  have hZaCore (neighbor : graph.Vertex)
      (hneighbor : graph.adjacent path.a neighbor) : z graph path.a ≤ q graph neighbor := by
    apply SevenSix.critical_minimality graph path
    have hdist := (SevenSix.adjacent_iff_distance_eq_one graph).mp hneighbor
    omega
  let intersection := q graph previous ⊓ q graph path.firstStep
  have hQnormal : q graph path.a ≤ Subgroup.normalizer (intersection : Set G) := by
    apply le_trans (le_inf
      ((core_le_neighbor ctx.sectionSeven graph hprevious).trans
        (SevenSix.stabilizer_le_normalizer_q graph previous))
      ((core_le_neighbor ctx.sectionSeven graph path.firstStep_adj).trans
        (SevenSix.stabilizer_le_normalizer_q graph path.firstStep)))
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hVfirstNormal : v graph path.firstStep ≤
      Subgroup.normalizer (intersection : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
      (hcomm.le.trans (hline.2.trans
        (le_inf (hZaCore previous hprevious) (hZaCore _ path.firstStep_adj))))
  have hVpreviousNormal : v graph previous ≤
      Subgroup.normalizer (intersection : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
      ((hneighborData previous hprev.1).1.le.trans
        ((hneighborData previous hprev.1).2.1.trans
          (le_inf (hZaCore previous hprevious) (hZaCore _ path.firstStep_adj))))
  let edge := stabilizer graph path.a ⊓ stabilizer graph path.firstStep
  have hVfirstEdge : v graph path.firstStep ≤ edge :=
    (hVcore _).trans (le_inf
      (core_le_neighbor ctx.sectionSeven graph (graph.adjacent_symm path.firstStep_adj))
      (core_le_self graph _))
  have hindices := cubic_edge_indices ctx.sectionSeven graph path.a path.firstStep
    path.firstStep_adj hquot
  have hedgeGen : q graph path.a ⊔ v graph path.firstStep = edge :=
    sup_eq_of_prime_relIndex _ _ _
      (le_inf (core_le_self graph _)
        (core_le_neighbor ctx.sectionSeven graph path.firstStep_adj))
      hVfirstEdge Nat.prime_two hindices.1 hnot
  have hedgeNormal : edge ≤ Subgroup.normalizer (intersection : Set G) := by
    rw [← hedgeGen]
    exact sup_le hQnormal hVfirstNormal
  have hVpreviousInitial : v graph previous ≤ stabilizer graph path.a :=
    (hVcore _).trans
      (core_le_neighbor ctx.sectionSeven graph (graph.adjacent_symm hprevious))
  have hVpreviousNotEdge : ¬ v graph previous ≤ edge := by
    intro hle
    apply (hneighborData previous hprev.1).2.2
    exact (le_inf hle ((hVcore _).trans (core_le_self graph _))).trans
      (cubic_fix_two ctx.sectionSeven graph path.a path.firstStep previous hquot
        path.firstStep_adj hprevious hprev.2.symm)
  have hgen : edge ⊔ v graph previous = stabilizer graph path.a :=
    sup_eq_of_prime_relIndex _ _ _ inf_le_left hVpreviousInitial
      Nat.prime_three hindices.2 hVpreviousNotEdge
  refine ⟨inf_le_left.trans
    (core_le_neighbor ctx.sectionSeven graph (graph.adjacent_symm hprevious)),
    Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
  change stabilizer graph path.a ≤ Subgroup.normalizer (intersection : Set G)
  rw [← hgen]
  exact sup_le hedgeNormal hVpreviousNormal

public theorem generated_eight_six_intersection_normal
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep) :
    NormalIn (QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a) :=
  eight_six_intersection_normal_local ctx.toLocalContext hcenter hquot hlength hcard previous hprev

end Stellmacher.SectionEight
