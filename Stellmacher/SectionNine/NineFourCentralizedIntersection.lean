module
public import Stellmacher.SectionNine.NineFourInitialResidualNeighbors
public import Stellmacher.SectionNine.NineThreeCoreOmega
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Theory.ThreeSubgroups

/-!
# The centralized neighboring-module intersection is the initial center

In the ambient Section Nine setting with critical distance greater than
one, let d be an initial-vertex neighbor distinct from the next vertex.
If the intersection of their modules centralizes Q_a intersect Q_d, that
intersection is exactly Z_a. No transvection action, counterexample, or
auxiliary group is assumed in this geometric step.

Each neighbor core normalizes the intersection because its module
commutators lie in the neighbor center, which is contained in Z_a and hence
in the intersection. The initial residual lies in their join, so together
with the initial core they make the intersection G_a-invariant. Put
J=[intersection,Q_a]. Three-subgroups, the assumed core-intersection
centralization, and the centrality of Z_a in Q_a give [J,Q_d]=1. Since J
is G_a-invariant, the residual conjugate-closure bound puts E_a in its
centralizer. The trivial residual centralizer (7.5)(c) kills J. Thus the
intersection lies in the core center and has exponent two; the proved
identity Ω₁(Z(Q_a))=Z_a gives the result.

This proves source (9.4)(6) and its repeated use in the all-central case,
Stellmacher, printed pp.51–52/PDF pp.41–42 of
`refs/files/stellmacher-n-group.pdf`. The final omega-center step makes the
source's implicit centralizer argument explicit without a new module action.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_centralized_intersection_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ remote,
      QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote⁆ = ⊥) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ remote = ZAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let Qd := QAt Γ remote
  let I := VAt Γ cp.firstStep ⊓ VAt Γ remote
  let Za := ZAt Γ cp.a
  let J := ⁅I,Qa⁆
  have hnMem : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hdAdj : Γ.adjacent cp.a remote := (mem_neighborhood_iff_adjacent Γ).mp hremote
  have hZaI : Za ≤ I := le_inf
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm cp.firstStep_adj))
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hdAdj))
  have hcenter := nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩
  have hZnZa : ZAt Γ cp.firstStep ≤ Za := (hcenter.2 cp.firstStep hnMem).2
  have hZdZa : ZAt Γ remote ≤ Za := (hcenter.2 remote hremote).2
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    hnMem hremote
  have hremoteOrbit : IsConjugateVertex Γ cp.firstStep remote := ⟨mover,hmover⟩
  have hnextComm : ⁅I,Qn⁆ ≤ ZAt Γ cp.firstStep :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).2.1
  have hremoteComm : ⁅I,Qd⁆ ≤ ZAt Γ remote :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb remote hremoteOrbit).2.1
  have hQnI : Qn ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hnextComm.trans (hZnZa.trans hZaI))
  have hQdI : Qd ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hremoteComm.trans (hZdZa.trans hZaI))
  have hQaNext : Qa ≤ GAt Γ cp.firstStep :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep hnMem default).2.2
  have hQaRemote : Qa ≤ GAt Γ remote :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote hremote default).2.2
  have hQaI : Qa ≤ Subgroup.normalizer (I : Set G) :=
    (le_inf (hQaNext.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
      (hQaRemote.trans (stabilizer_le_normalizer_v Γ remote))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hres := nine_four_initial_residual_neighbors ctx hb remote hremote hne
  have hEI : EAt Γ cp.a ≤ Subgroup.normalizer (I : Set G) :=
    hres.1.trans (sup_le hQnI hQdI)
  have hSI : T ≤ Subgroup.normalizer (I : Set G) :=
    (cp.S_le_edge_stabilizers.trans_eq (nine_initial_edge_core_product ctx hb).1.symm).trans
      (sup_le hQaI hQnI)
  have hgen : EAt Γ cp.a ⊔ T = P := by
    change e Γ cp.a ⊔ T = stabilizer Γ cp.a
    rw [CosetGraphContext.e,Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hPI : P ≤ Subgroup.normalizer (I : Set G) := by
    rw [← hgen]
    exact sup_le hEI hSI
  have hQaP : Qa ≤ P := by
    change q Γ cp.a ≤ stabilizer Γ cp.a
    rw [q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQdP : Qd ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core remote cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hdAdj)) default).2.2
  have hcoreComm : ⁅Qa,Qd⁆ ≤ Qa ⊓ Qd :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQdP.trans (stabilizer_le_normalizer_q Γ cp.a)))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hQaRemote.trans (stabilizer_le_normalizer_q Γ remote)))
  have hZaQa : ⁅Za,Qa⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff Qa z).mp
        ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hnMem hz)).2.2
  have hJQd : ⁅J,Qd⁆ = ⊥ := by
    apply Subgroup.commutator_commutator_eq_bot_of_rotate
    · apply bot_unique
      rw [Subgroup.commutator_comm] at hcomm
      exact (Subgroup.commutator_mono hcoreComm le_rfl).trans_eq hcomm
    · apply bot_unique
      have hh : ⁅Qd,I⁆ ≤ Za := by
        rw [Subgroup.commutator_comm]
        exact hremoteComm.trans hZdZa
      exact (Subgroup.commutator_mono hh le_rfl).trans_eq hZaQa
  have hPJ : P ≤ Subgroup.normalizer (J : Set G) := by
    intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (⁅I,Qa⁆).map (MulAut.conj g).toMonoidHom = ⁅I,Qa⁆
    have hImap : I.map (MulAut.conj g).toMonoidHom = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPI hg)
    have hQamap : Qa.map (MulAut.conj g).toMonoidHom = Qa :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (stabilizer_le_normalizer_q Γ cp.a hg)
    rw [Subgroup.map_commutator,hImap,hQamap]
  have hPC : P ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) :=
    hPJ.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (J : Set G)))
  have hQdC : Qd ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJQd)
  have hclosureC : conjugateClosure Qd P ≤ Subgroup.centralizer (J : Set G) := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨g,q,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPC g.property) q).mp (hQdC q.property)
  have hJE : J ≤ Subgroup.centralizer (EAt Γ cp.a : Set G) :=
    Subgroup.le_centralizer_iff.mp (hres.2.trans hclosureC)
  have hJI : J ≤ I := Subgroup.le_normalizer_iff_commutator_le_left.mp hQaI
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hIQa : I ≤ Qa :=
    inf_le_left.trans ((nine_seven_neighbor_module_le_neighborhood Γ cp.firstStep_adj).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a))
  have hJbot : J = ⊥ := bot_unique
    ((le_inf (hJI.trans hIQa) hJE).trans_eq
      (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).centralizer_residual)
  have hIQaCentral : I ≤ Subgroup.centralizer (Qa : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJbot
  have hIomega : I ≤ omegaOneCenter Qa := by
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff Qa z).mpr
    exact ⟨hIQa hz,elemPow_eq_one_of_isElementaryAbelian z hz.1,
      Subgroup.mem_centralizer_iff.mp (hIQaCentral hz)⟩
  exact le_antisymm
    (hIomega.trans_eq (nine_three_core_omega_eq_center ctx hb cp.a ⟨1,Γ.act_one _⟩)) hZaI

end Stellmacher.SectionNine
