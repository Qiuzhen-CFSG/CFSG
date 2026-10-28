module

public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# Ambient Sylow pairs from genuine terminal edges

For a Sylow terminal context, any adjacent pair of vertex stabilizers whose
intersection is a two-group maps to a pair with ambient Sylow intersection.
The join of the mapped pair has trivial two-core, and the resulting Sylow
has the same order as the prescribed ambient Sylow. This is the common
embedding step in the source-local realizations of (9.1) and (10.1)(a).

Section 7 conjugates the selected edge intersection to the intersection of
the original pair inside its actual join. Two-groupness therefore transfers
to the original ambient pair, where maximality of the prescribed Sylow
identifies the intersection. Mapping the edge conjugation gives a conjugate
of that ambient Sylow. Actual edge generation makes the mapped join the
original join, whose two-core is trivial by the native Section 7 hypothesis.
The selected edge need not equal the original prescribed Sylow.

Source: the local-type definitions after Stellmacher (8.6), (9.1), and (10.1),
and their Section 11 realization. The existing construction in
`Stellmacher.SectionEleven.MultipleTenOneRealization` supplies the same
argument for (10.1)(b); this module exposes its common edge step without
altering that proof.
-/

namespace Stellmacher.SectionEleven

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- A two-group terminal edge supplies a genuine ambient Sylow intersection
and a join with trivial two-core. -/
public theorem sylow_terminal_edge_pair
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    {a b : ctx.Γ.Vertex} (hab : ctx.Γ.adjacent a b)
    (htwo : IsPGroup 2 (GAt ctx.Γ a ⊓ GAt ctx.Γ b : Subgroup (P1 ⊔ P2 : Subgroup H))) :
    ∃ R : Sylow 2 H,
      (GAt ctx.Γ a).map (P1 ⊔ P2).subtype ⊓
        (GAt ctx.Γ b).map (P1 ⊔ P2).subtype = (R : Subgroup H) ∧
      pCore 2 (↥((GAt ctx.Γ a).map (P1 ⊔ P2).subtype ⊔
        (GAt ctx.Γ b).map (P1 ⊔ P2).subtype)) = ⊥ ∧
      Nat.card R = Nat.card S0 := by
  let graph := ctx.Γ
  let joinGroup := P1 ⊔ P2
  let first := P1.subgroupOf joinGroup
  let second := P2.subgroupOf joinGroup
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one ctx.sectionSeven graph).edge_stabilizers_conjugate a b hab
  have hbaseTwo : IsPGroup 2 (first ⊓ second : Subgroup joinGroup) := by
    change IsPGroup 2 (graph.stabilizer a ⊓ graph.stabilizer b : Subgroup joinGroup) at htwo
    rw [hactor] at htwo
    exact htwo.of_equiv ((MulAut.conj actor).subgroupMap (first ⊓ second)).symm
  have hbaseMap : (first ⊓ second).map joinGroup.subtype = P1 ⊓ P2 := by
    rw [Subgroup.map_inf _ _ _ joinGroup.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right]
  have hambientTwo : IsPGroup 2 (P1 ⊓ P2 : Subgroup H) := by
    rw [← hbaseMap]
    exact hbaseTwo.map joinGroup.subtype
  have hbaseSylow : P1 ⊓ P2 = (S0 : Subgroup H) :=
    S0.is_maximal' hambientTwo (le_inf
      ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
      ctx.hypothesisTwo.fiveOne.P2_mem.1.2.1.1)
  have hmapConj : joinGroup.subtype.comp (MulAut.conj actor).toMonoidHom =
      (MulAut.conj (actor : H)).toMonoidHom.comp joinGroup.subtype := by
    ext element
    rfl
  have hintersection :
      (GAt graph a ⊓ GAt graph b).map joinGroup.subtype =
        (((actor : H) • S0 : Sylow 2 H) : Subgroup H) := by
    change (graph.stabilizer a ⊓ graph.stabilizer b).map _ = _
    rw [hactor]
    change ((first ⊓ second).map (MulAut.conj actor).toMonoidHom).map _ = _
    rw [Subgroup.map_map, hmapConj, ← Subgroup.map_map, hbaseMap, hbaseSylow]
    rfl
  have hneighbor : b ∈ graph.neighborhood a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr hab
  have hgenerate : GAt graph a ⊔ GAt graph b = ⊤ :=
    (edge_sectionThree_data ctx.sectionSeven graph hneighbor
      (default : Sylow 2 (↥(graph.stabilizer a ⊓ graph.stabilizer b)))).2.2.2.2.1
  have hjoin : (GAt graph a).map joinGroup.subtype ⊔
      (GAt graph b).map joinGroup.subtype = joinGroup := by
    rw [← Subgroup.map_sup, hgenerate]
    simpa [MonoidHom.range_eq_map] using Subgroup.range_subtype (H := joinGroup)
  refine ⟨(actor : H) • S0, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ _ joinGroup.subtype_injective]
    exact hintersection
  · change pCore 2 (↥((GAt graph a).map joinGroup.subtype ⊔
      (GAt graph b).map joinGroup.subtype)) = ⊥
    rw [hjoin]
    exact ctx.sectionSeven.twoCore_eq_bot
  · exact ((actor : H) • S0).card_eq_multiplicity.trans S0.card_eq_multiplicity.symm

end Stellmacher.SectionEleven
