module

public import Stellmacher.SectionNine.CubicLocalAction
public import Stellmacher.SectionFiveToSeven.Result7_6

/-!
# Cubic core-intersection noncontainment

Under genuine Section Seven hypotheses, fix a critical path and assume that
every vertex stabilizer modulo its two-core is `SL₂(2)`. For distinct neighbors
`left` and `right` of a vertex `middle` in the first-step orbit, the intersection
of the cores at `left` and `middle` is not contained in the core at `right`.
Together with adjacent-core incomparability and an edge stabilizer outside
its core, this supplies the three local actions in the four-path argument.

The actual S3 quotients give equal core orders on each edge. Equality of
adjacent cores would transport to the distinguished critical edge, violating
(7.6). Thus adjacent cores are incomparable. An adjacent core cannot fix two
neighbors without fixing all three; the edge stabilizer has index three, so
the adjacent core and a different edge stabilizer generate the local group.
This proves the generation hypothesis in (7.6)(c). Transporting an oriented
edge to any vertex in the first-step orbit gives the three-vertex
core-intersection noncontainment. Source: Stellmacher, printed p.54 / PDF
p.44, with the proved scan-correct (7.6)(c); no later numbered result is used.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

variable {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}

private theorem mem_stabilizer (Γ : CosetGraphContext G S P1 P2)
    {actor : G} {vertex : Γ.Vertex} :
    actor ∈ GAt Γ vertex ↔ Γ.act actor vertex = vertex :=
  Set.ext_iff.mp (Γ.stabilizer_def vertex) actor

private theorem core_le_self (Γ : CosetGraphContext G S P1 P2)
    (vertex : Γ.Vertex) : QAt Γ vertex ≤ GAt Γ vertex := by
  rw [QAt, q, Γ.twoCoreAt_def]
  exact SevenSix.twoCoreIn_le _

private theorem core_le_neighbor (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) {left right : Γ.Vertex}
    (hadj : Γ.adjacent left right) : QAt Γ left ≤ GAt Γ right :=
  ((lemma_seven_three h7 Γ).sylow_and_core left right
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hadj) default).2.2

public theorem adjacent_cores_incomparable
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hmodels : ∀ vertex, QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two)
    {left right : Γ.Vertex} (hadj : Γ.adjacent left right) :
    ¬ QAt Γ left ≤ QAt Γ right := by
  have hcardleft := (cubic_local_action_of_sl2Two_quotient Γ h7 left
    (hmodels left)).edge_card right hadj
  have hcardright := (cubic_local_action_of_sl2Two_quotient Γ h7 right
    (hmodels right)).edge_card left (Γ.adjacent_symm hadj)
  rw [inf_comm] at hcardright
  unfold QuotientCardEq at hcardleft hcardright
  have hcards : Nat.card (QAt Γ left) = Nat.card (QAt Γ right) := by omega
  intro hle
  have heq := Subgroup.eq_of_le_of_card_ge hle hcards.ge
  obtain ⟨actor, horiented | hreversed⟩ :=
    (lemma_seven_one h7 Γ).edge_not_vertex_transitive.1 hadj cp.firstStep_adj
  all_goals
    have hmap := congrArg (fun subgroup : Subgroup G =>
      subgroup.map (MulAut.conj actor⁻¹).toMonoidHom) heq
    rw [← SevenSix.q_act, ← SevenSix.q_act] at hmap
  · rw [horiented.1, horiented.2] at hmap
    apply (lemma_seven_six h7 Γ cp).core_intersection_not_normal
    rw [hmap, inf_idem]
    refine ⟨core_le_self Γ _, ?_⟩
    change ((Γ.twoCoreAt cp.firstStep).subgroupOf _).Normal
    rw [Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_normal _
  · rw [hreversed.1, hreversed.2] at hmap
    apply (lemma_seven_six h7 Γ cp).core_intersection_not_normal
    rw [← hmap, inf_idem]
    refine ⟨core_le_self Γ _, ?_⟩
    change ((Γ.twoCoreAt cp.firstStep).subgroupOf _).Normal
    rw [Γ.twoCoreAt_def]
    exact SevenSix.twoCoreIn_normal _

public theorem edge_stabilizer_outside_core
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    {left right : Γ.Vertex} (hadj : Γ.adjacent left right)
    (hmodel : QuotientIsModel (GAt Γ left) (QAt Γ left) SL2Two) :
    ¬ GAt Γ left ⊓ GAt Γ right ≤ QAt Γ left := by
  intro hle
  have heq := le_antisymm hle
    (le_inf (core_le_self Γ left) (core_le_neighbor h7 Γ hadj))
  have hcard := (cubic_local_action_of_sl2Two_quotient Γ h7 left hmodel).edge_card
    right hadj
  unfold QuotientCardEq at hcard
  rw [heq] at hcard
  have hpos := Nat.card_pos (α := QAt Γ left)
  omega

public theorem cubic_edge_index_three
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    {left right : Γ.Vertex} (hadj : Γ.adjacent left right)
    (hmodel : QuotientIsModel (GAt Γ left) (QAt Γ left) SL2Two) :
    (GAt Γ left ⊓ GAt Γ right).relIndex (GAt Γ left) = 3 := by
  have hedge := (cubic_local_action_of_sl2Two_quotient Γ h7 left hmodel).edge_card
    right hadj
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hgroup := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (core_le_self Γ left)).toEquiv,
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hgroup
  have hindex := ((GAt Γ left ⊓ GAt Γ right).subgroupOf (GAt Γ left)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show GAt Γ left ⊓ GAt Γ right ≤ GAt Γ left from inf_le_left)).toEquiv] at hindex
  change (GAt Γ left ⊓ GAt Γ right).relIndex (GAt Γ left) * _ = _ at hindex
  change Nat.card (GAt Γ left ⊓ GAt Γ right : Subgroup G) =
    2 * Nat.card (QAt Γ left) at hedge
  rw [hedge] at hindex
  have hpos := Nat.card_pos (α := QAt Γ left)
  nlinarith

private theorem neighbor_core_generates_with_other_edge
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hmodels : ∀ vertex, QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two)
    {left middle right : Γ.Vertex}
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hne : left ≠ right) :
    QAt Γ right ⊔ (GAt Γ left ⊓ GAt Γ middle) = GAt Γ middle := by
  let edge : Subgroup G := GAt Γ left ⊓ GAt Γ middle
  let generated : Subgroup G := QAt Γ right ⊔ edge
  have hle : generated ≤ GAt Γ middle :=
    sup_le (core_le_neighbor h7 Γ (Γ.adjacent_symm hright)) inf_le_right
  have hout : ¬ QAt Γ right ≤ QAt Γ middle :=
    adjacent_cores_incomparable h7 Γ cp hmodels (Γ.adjacent_symm hright)
  have hnotedge : ¬ QAt Γ right ≤ edge := by
    intro hcontained
    apply hout
    intro actor hactor
    have hfixleft := (mem_stabilizer Γ).1 (hcontained hactor).1
    have hfixright := (mem_stabilizer Γ).1 (core_le_self Γ right hactor)
    have hfixmiddle := core_le_neighbor h7 Γ (Γ.adjacent_symm hright) hactor
    apply ((cubic_local_action_of_sl2Two_quotient Γ h7 middle
      (hmodels middle)).kernel ⟨actor, hfixmiddle⟩).2
    intro neighbor hneighbor
    by_cases hsame : neighbor = left
    · simpa only [hsame] using hfixleft
    by_cases hsameright : neighbor = right
    · simpa only [hsameright] using hfixright
    have hdegree := (cubic_local_action_of_sl2Two_quotient Γ h7 middle
      (hmodels middle)).degree
    classical
    let Points := {vertex // Γ.adjacent middle vertex}
    let : Finite Γ.Vertex := Γ.finiteVertex
    let := Fintype.ofFinite Points
    have hcover : ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} :
        Finset Points) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← Nat.card_eq_fintype_card, hdegree]
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
      rwa [(mem_stabilizer Γ).1 hfixmiddle] at htransport
    have hmem : (⟨Γ.act actor neighbor, hacted⟩ : Points) ∈
        ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} : Finset Points) := by
      rw [hcover]; exact Finset.mem_univ _
    have hinj : Function.Injective (Γ.act actor) := by
      intro first second heq
      have hinv := congrArg (Γ.act actor⁻¹) heq
      simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    rcases hmem with heq | heq | heq
    · exact (hsame (hinj (heq.trans hfixleft.symm))).elim
    · exact (hsameright (hinj (heq.trans hfixright.symm))).elim
    · exact heq
  have hindex : edge.relIndex (GAt Γ middle) = 3 := by
    dsimp [edge]
    rw [inf_comm]
    exact cubic_edge_index_three h7 Γ hleft (hmodels middle)
  have htower := Subgroup.relIndex_mul_relIndex edge generated (GAt Γ middle)
    le_sup_right hle
  rw [hindex] at htower
  have hdiv : edge.relIndex generated ∣ 3 := ⟨_, htower.symm⟩
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hdiv) with hone | hthree
  · exact (hnotedge (le_sup_left.trans (Subgroup.relIndex_eq_one.mp hone))).elim
  · rw [hthree] at htower
    have hone : generated.relIndex (GAt Γ middle) = 1 := by omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

public theorem cubic_core_intersection_noncontainment
    (h7 : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hmodels : ∀ vertex, QuotientIsModel (GAt Γ vertex) (QAt Γ vertex) SL2Two)
    {left middle right : Γ.Vertex}
    (horbit : IsConjugateVertex Γ cp.firstStep middle)
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hne : left ≠ right) :
    ¬ QAt Γ left ⊓ QAt Γ middle ≤ QAt Γ right := by
  obtain ⟨first, hfirst⟩ := horbit
  have hfirstleft : Γ.adjacent middle (Γ.act first cp.a) := by
    have hedge := adjacent_act Γ first (Γ.adjacent_symm cp.firstStep_adj)
    rwa [hfirst] at hedge
  obtain ⟨second, hsecond⟩ := (lemma_seven_one h7 Γ).local_transitivity middle
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hfirstleft)
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hleft)
  let actor : G := first * (second : G)
  have hmiddle : Γ.act actor cp.firstStep = middle := by
    change Γ.act (first * (second : G)) cp.firstStep = middle
    rw [Γ.act_mul, hfirst]
    exact (mem_stabilizer Γ).1 second.property
  have hleft' : Γ.act actor cp.a = left := by
    change Γ.act (first * (second : G)) cp.a = left
    rw [Γ.act_mul, hsecond]
  let back := Γ.act actor⁻¹ right
  have hback : Γ.act actor back = right := by
    simp only [back, ← Γ.act_mul, inv_mul_cancel, Γ.act_one]
  have hbackadj : Γ.adjacent cp.firstStep back := by
    have hedge := adjacent_act Γ actor⁻¹ hright
    rw [← hmiddle] at hedge
    simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hedge
  have hbackne : cp.a ≠ back := by
    intro heq
    apply hne
    rw [← hleft', heq, hback]
  have hgen := neighbor_core_generates_with_other_edge h7 Γ cp hmodels
    (Γ.adjacent_symm cp.firstStep_adj) hbackadj hbackne
  have hnon := (lemma_seven_six h7 Γ cp).neighbor_core_noncontainment back
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).2 hbackadj) hgen
  intro hle
  apply hnon
  apply (Subgroup.map_le_map_iff_of_injective
    (f := (MulAut.conj actor⁻¹).toMonoidHom) (MulAut.conj actor⁻¹).injective).mp
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective,
    ← SevenSix.q_act, ← SevenSix.q_act, ← SevenSix.q_act,
    hleft', hmiddle, hback]
  exact hle

end Stellmacher.SectionNine
