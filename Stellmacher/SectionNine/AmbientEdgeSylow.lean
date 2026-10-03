module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct
public import Stellmacher.SectionNine.NineTwoAmbientSetup

/-!
# Edge stabilizers as Sylow subgroups of the ambient group

In the ambient Section Nine context with critical length greater than one,
the stabilizer intersection of any adjacent vertices maps to an actual
Sylow two-subgroup of H. The supplied embedding is retained; the graph
group need not be the whole ambient group.

The initial edge is the join of its two vertex cores. Both cores lie in
the distinguished graph Sylow T, so this entire edge equals T. The initial
stabilizer orientation identifies the base intersection A∩B with T, and
(7.1) conjugates every edge stabilizer to this base intersection. Mapping
that conjugation through the embedding and using the proved ambient
identity S=S₀ produces the required conjugate of S₀.

This combines Stellmacher (7.1), (9.2), and the edge-core product after
(9.3), Journal of Algebra 190 (1997), printed pp.48–50. It supplies the
ambient Sylow property used for the normalizer argument in (10.1)(a3)(9),
printed pp.61–62, without any transfer of the ambient local hypotheses.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- Every embedded edge stabilizer is a Sylow two-subgroup of the original ambient group. -/
public theorem ambient_edge_stabilizer_is_sylow_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (d l : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d l) :
    ∃ P : Sylow 2 H,
      (P : Subgroup H) = (GAt ctx.Γ d ⊓ GAt ctx.Γ l).map embedding := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hjoin := (nine_initial_edge_core_product ctx hb).1
  have hcores := local_cores_le_edge_sylow ctx.sectionSeven Γ cp
  have hTedge : T = GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    le_antisymm cp.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
  have hbase : A ⊓ B = T := by
    change T = stabilizer Γ cp.a ⊓ stabilizer Γ cp.firstStep at hTedge
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2] at hTedge
      exact hTedge.symm
    · rw [hedge.1, hedge.2] at hTedge
      exact (inf_comm A B).trans hTedge.symm
  obtain ⟨actor, hactor⟩ :=
    (lemma_seven_one ctx.sectionSeven Γ).edge_stabilizers_conjugate d l hadj
  have hglobal := (nine_two_ambient_setup ctx).1
  have hmapConj : embedding.comp (MulAut.conj actor).toMonoidHom =
      (MulAut.conj (embedding actor)).toMonoidHom.comp embedding := by
    ext element
    simp
  refine ⟨embedding actor • S0, ?_⟩
  symm
  change (Γ.stabilizer d ⊓ Γ.stabilizer l).map embedding = _
  rw [hactor]
  change ((A ⊓ B).map (MulAut.conj actor).toMonoidHom).map embedding = _
  rw [Subgroup.map_map, hmapConj, ← Subgroup.map_map, hbase, ctx.map_S, hglobal]
  rfl

end Stellmacher.SectionNine
