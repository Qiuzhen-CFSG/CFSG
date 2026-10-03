module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct
public import Stellmacher.SectionNine.NineNextFaithfulQuotient

/-!
# The remote core acts through an active index-two quotient

For any neighbor d of the initial critical vertex, Q_a intersect Q_d
has index two in Q_d and Q_d does not centralize Z_a. The theorem uses
the actual Section Nine context and critical distance greater than one;
it does not require an actor or counterexample.

The proved initial edge-core product and cardinality formula give the
index two statement at the next vertex by the relative-index diamond.
Local transitivity supplies an element of G_a carrying that neighbor to d.
It normalizes Q_a and Z_a, so conjugation transports both the index and
the already established nontrivial initial-center/next-core commutator.

These are the geometric inputs for the fixed-subgroup decomposition in
the all-central case of Stellmacher (9.4), printed p.52 / PDF p.42 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_remote_core_action_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex) (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote).relIndex (QAt ctx.Γ remote) = 2 ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a,QAt ctx.Γ remote⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let Qd := QAt Γ remote
  let Za := ZAt Γ cp.a
  have hindex : Qa.relIndex Qn = 2 := by
    have hproduct := nine_initial_edge_core_product ctx hb
    have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
    have hcount := (Qa.subgroupOf (GAt Γ cp.a ⊓ GAt Γ cp.firstStep)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQaEdge).toEquiv] at hcount
    have hQaIndex : Qa.relIndex (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = 2 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hproduct.2)
    have hQnEdge : Qn ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers
    let P := Qa ⊔ Qn
    let _ : (Qa.subgroupOf P).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le Qa.le_normalizer
          (hQnEdge.trans (inf_le_left.trans (stabilizer_le_normalizer_q Γ cp.a))))
    have h := Subgroup.relIndex_sup_left (Qn.subgroupOf P) (Qa.subgroupOf P)
    rw [← Subgroup.subgroupOf_sup (show Qa ≤ P from le_sup_left)
      (show Qn ≤ P from le_sup_right), Subgroup.relIndex_subgroupOf le_rfl,
      Subgroup.relIndex_subgroupOf (show Qn ≤ P from le_sup_right)] at h
    change Qa.relIndex (Qa ⊔ Qn) = Qa.relIndex Qn at h
    rw [show Qa ⊔ Qn = GAt Γ cp.a ⊓ GAt Γ cp.firstStep from hproduct.1,hQaIndex] at h
    exact h.symm
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hremote
  let e := (MulAut.conj ((mover : G)⁻¹)).toMonoidHom
  have hQa : Qa.map e = Qa := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_le_normalizer_q Γ cp.a ((GAt Γ cp.a).inv_mem mover.property))
  have hZa : Za.map e = Za := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (stabilizer_le_normalizer_z Γ cp.a ((GAt Γ cp.a).inv_mem mover.property))
  have hQd : Qn.map e = Qd := by
    change (q Γ cp.firstStep).map (MulAut.conj ((mover : G)⁻¹)).toMonoidHom = q Γ remote
    rw [← q_act,hmover]
  have hindexRemote : Qa.relIndex Qd = 2 := by
    rw [← hQa,← hQd,Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj ((mover : G)⁻¹)).injective]
    exact hindex
  refine ⟨by simpa only [Subgroup.inf_relIndex_right] using hindexRemote,?_⟩
  intro hbot
  apply nine_initial_next_core_commutator_ne_bot ctx.toLocalContext
  apply Subgroup.map_injective (f := e) (MulAut.conj ((mover : G)⁻¹)).injective
  change (⁅Za,Qn⁆).map e = (⊥ : Subgroup G).map e
  rw [Subgroup.map_commutator,hZa,hQd,Subgroup.map_bot]
  exact hbot

end Stellmacher.SectionNine
