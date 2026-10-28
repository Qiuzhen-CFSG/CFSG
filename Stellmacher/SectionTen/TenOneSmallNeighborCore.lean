module
public import Stellmacher.SectionTen.TenOneSmallDerived

/-!
# Neighbor-core slices and indices in the small branch of Stellmacher (10.1)

In the actual ambient distance-three geometry, a middle neighbor module is
not contained in the core at any other middle neighbor. If the first module
has order eight, every such module/core intersection is the middle center.
If the first local core quotient is SL₂(2), every neighbor core has relative
index two in the actual generated neighborhood group. This last index result
does not require the order-eight hypothesis.

Ordered-pair alignment under the middle stabilizer transports the original
critical noncontainment and the proved small seed equality. For the index,
local transitivity transports the first cubic edge cardinality to each
neighbor edge. Critical distance three puts the neighborhood group in the
middle core and hence inside that edge, bounding its relative index by two.
A distinct neighbor module escapes the given core, ruling out index one.

These are the geometric inputs to the three-kernel index calculation in the
small case (6) of Stellmacher (10.1), printed p.60/PDF p.50 of
`refs/files/stellmacher-n-group.pdf`. The common index assembly is separate.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- Any two distinct middle neighbors retain the critical module/core escape. -/
public theorem ten_one_neighbor_module_not_le_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) : ¬ VAt ctx.Γ left ≤ QAt ctx.Γ right := by
  obtain ⟨actor, _, hfirst, hterminal⟩ :=
    ten_one_neighbor_pair_alignment ctx middle hpath hleft hright hne
  intro hle
  apply (sectionTenOpeningData ctx middle hpath).first_noncontainment
  rw [← hfirst, ← hterminal, VAt, QAt, v_act, q_act] at hle
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle

/-- In the order-eight branch, every cross-neighbor module/core slice is the middle center. -/
public theorem ten_one_small_neighbor_core_slice
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    {left right : ctx.Γ.Vertex}
    (hleft : ctx.Γ.adjacent middle left) (hright : ctx.Γ.adjacent middle right)
    (hne : left ≠ right) :
    VAt ctx.Γ left ⊓ QAt ctx.Γ right = ZAt ctx.Γ middle := by
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hseed : VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a' =
      ZAt ctx.Γ middle := by
    apply le_antisymm
    · rw [← ten_one_small_generated_eq_center ctx middle hpath hsmall]
      intro element helement
      apply Subgroup.subset_closure
      refine ⟨1, ⟨element, helement⟩, ?_⟩
      simp
    · rw [← ten_one_small_intersection ctx middle hpath hsmall]
      exact inf_le_inf_left _
        (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb ctx.criticalPath.a')
  obtain ⟨actor, hactor, hfirst, hterminal⟩ :=
    ten_one_neighbor_pair_alignment ctx middle hpath hleft hright hne
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_le_normalizer_z ctx.Γ middle ((GAt ctx.Γ middle).inv_mem hactor))
  rw [← hfirst, ← hterminal, VAt, QAt, v_act, q_act,
    ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective]
  change (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a').map _ = _
  rw [hseed]
  exact hmap

private theorem core_le_self
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) : QAt ctx.Γ vertex ≤ GAt ctx.Γ vertex := by
  rw [QAt, q, ctx.Γ.twoCoreAt_def]
  exact twoCoreIn_le _

private theorem core_le_neighbor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    {vertex neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent vertex neighbor) :
    QAt ctx.Γ vertex ≤ GAt ctx.Γ neighbor :=
  ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core vertex neighbor
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) default).2.2

private theorem neighbor_edge_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    {neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor) :
    Nat.card (GAt ctx.Γ neighbor ⊓ GAt ctx.Γ middle : Subgroup G) =
      2 * Nat.card (QAt ctx.Γ neighbor) := by
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hcard := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
    ctx.criticalPath.firstStep hmodel).edge_card middle (ctx.Γ.adjacent_symm hfirst)
  obtain ⟨actor, hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj)
  have hfix : ctx.Γ.act (actor : G) middle = middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp actor.property
  calc
    _ = Nat.card ((GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ middle).map
        (MulAut.conj (actor : G)⁻¹).toMonoidHom) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (actor : G)⁻¹).injective]
      change Nat.card _ = Nat.card ((stabilizer ctx.Γ ctx.criticalPath.firstStep).map _ ⊓
        (stabilizer ctx.Γ middle).map _ : Subgroup G)
      have hleftMap := stabilizer_act ctx.Γ (actor : G) ctx.criticalPath.firstStep
      have hrightMap := stabilizer_act ctx.Γ (actor : G) middle
      change _ = (stabilizer ctx.Γ ctx.criticalPath.firstStep).map _ at hleftMap
      change _ = (stabilizer ctx.Γ middle).map _ at hrightMap
      rw [← hleftMap, ← hrightMap, hmove, hfix]
    _ = Nat.card (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ middle : Subgroup G) :=
      Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective
    _ = 2 * Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) := hcard
    _ = 2 * Nat.card (QAt ctx.Γ neighbor) := by
      rw [← hmove]
      change 2 * Nat.card (q ctx.Γ ctx.criticalPath.firstStep) =
        2 * Nat.card (q ctx.Γ (ctx.Γ.act (actor : G) ctx.criticalPath.firstStep))
      rw [q_act, Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective]

/-- A cubic first quotient gives index two for every neighbor core in the neighborhood group. -/
public theorem ten_one_small_neighbor_core_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    {neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor) :
    (QAt ctx.Γ neighbor).relIndex (GeneratedNeighborhoodV ctx.Γ middle) = 2 := by
  let edge := GAt ctx.Γ neighbor ⊓ GAt ctx.Γ middle
  let Q := QAt ctx.Γ neighbor
  let W := GeneratedNeighborhoodV ctx.Γ middle
  have hQE : Q ≤ edge := le_inf (core_le_self ctx neighbor)
    (core_le_neighbor ctx (ctx.Γ.adjacent_symm hadj))
  have hindex : Q.relIndex edge = 2 := by
    have hcount := (Q.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv] at hcount
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (hcount.trans (neighbor_edge_card ctx middle hpath hmodel hadj))
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hWQ : W ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hWE : W ≤ edge := hWQ.trans
    (le_inf (core_le_neighbor ctx hadj) (core_le_self ctx middle))
  have hbound := Subgroup.relIndex_le_of_le_right (H := Q) hWE
    (show Q.relIndex edge ≠ 0 by rw [hindex]; decide)
  rw [hindex] at hbound
  have hnot : ¬ W ≤ Q := by
    obtain ⟨_, hfirst, hterminal, hne⟩ := sectionTenOpeningGeometry ctx middle hpath
    obtain ⟨other, hother, hne⟩ : ∃ other, ctx.Γ.adjacent middle other ∧ other ≠ neighbor := by
      by_cases heq : ctx.criticalPath.firstStep = neighbor
      · exact ⟨ctx.criticalPath.a', hterminal, heq ▸ hne.symm⟩
      · exact ⟨ctx.criticalPath.firstStep, hfirst, heq⟩
    intro hle
    exact ten_one_neighbor_module_not_le_core ctx middle hpath hother hadj hne
      ((show VAt ctx.Γ other ≤ W from
        le_sSup ⟨other, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hother, rfl⟩).trans hle)
  have hneone := mt (Subgroup.relIndex_eq_one (H := Q) (K := W)).mp hnot
  have hnezero : Q.relIndex W ≠ 0 := (Q.subgroupOf W).index_ne_zero_of_finite
  change Q.relIndex W = 2
  omega
end Stellmacher.SectionTen
