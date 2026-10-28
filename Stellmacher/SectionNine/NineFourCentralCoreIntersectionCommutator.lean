module
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineFourActorClosureAction
public import Stellmacher.SectionNine.NineFourActorClosure
public import Stellmacher.SectionNine.NineFourCentralNormalization
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Theory.ThreeSubgroups

/-!
# Centralizing the initial/remote core intersection in central (9.4)

For an exact normalized counterexample to (9.4), assume the all-central
commutator bound [A,O₂(O²(F))]≤Z_next, the actual actor-cover, and the
proved residual/core generation of F. Then A centralizes the initial /
remote core intersection R0. The source index-at-least-four bound is
retained; no stronger identification of the auxiliary two-core is assumed.

Put D0=R0 intersect Q_next. The actor closure centralizes A, and its cover
of R0 reduces the problem to [A,D0]. The subgroup D0 lies in O₂(F), so
relative three-subgroups gives [[A,D0],O²(F)]≤Z_next, using the supplied
all-central bound and the auxiliary normalization theorem. If [A,D0]
were nontrivial it would equal the remote center, a subgroup of order two.
Adjoining Z_next then gives Z_a and makes it invariant under O²(F).
The other generators R0 and F intersect Q_next lie in G_a and normalize
Z_a. The exact weak residual/core supplement therefore makes F normalize
Z_a. Edge-plus-actor generation gives normalization by G_next; the proved
neighbor-module spanning theorem would put V_next in Z_a, contradicting
the source index bound.

This proves the central commutator step on printed p.52 / PDF p.42 of
Stellmacher (9.4), `refs/files/stellmacher-n-group.pdf`. It explicitly
handles the quotient-kernel term in the established generation equality.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise
universe u

private theorem sup_commutator_le {G : Type*} [Group G]
    (P U W D Z : Subgroup G) (hPZ : P ≤ Subgroup.normalizer Z)
    (hUP : U ≤ P) (hWP : W ≤ P)
    (hUD : ⁅U,D⁆ ≤ Z) (hWD : ⁅W,D⁆ ≤ Z) : ⁅U ⊔ W,D⁆ ≤ Z :=
  (Subgroup.commutator_mono (sup_le
    (Subgroup.le_commutatorPreimage hUP hUD)
    (Subgroup.le_commutatorPreimage hWP hWD)) le_rfl).trans
      (Subgroup.commutator_commutatorPreimage_le P D Z hPZ)

public theorem nine_four_central_core_intersection_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)) :
    let R0 := QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)
    let F := R0 ⊔ Subgroup.zpowers data.actor
    let Qn := QAt ctx.Γ ctx.criticalPath.firstStep
    let Q := twoCoreIn (twoResidualIn F)
    let T0 := conjugateClosure (Subgroup.zpowers (data.conjugator⁻¹*data.actor*data.conjugator))
      (QAt ctx.Γ ctx.criticalPath.a)
    ⁅data.subgroup,Q⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep →
    R0 ≤ T0 ⊔ Qn →
    F = (twoResidualIn F ⊔ R0) ⊔ (F ⊓ Qn) →
    ⁅data.subgroup,R0⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let Qd := QAt Γ d
  let Vn := VAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let Zn := ZAt Γ cp.firstStep
  let Zd := ZAt Γ d
  let A := data.subgroup
  let R0 := Qa ⊓ Qd
  let F := R0 ⊔ Subgroup.zpowers data.actor
  let E := twoResidualIn F
  let Q := twoCoreIn E
  let T0 := conjugateClosure (Subgroup.zpowers (data.conjugator⁻¹*data.actor*data.conjugator)) Qa
  let D0 := R0 ⊓ Qn
  let J := ⁅A,D0⁆
  dsimp only
  intro hcentral hcover hgeneration
  have hFP : F ≤ GAt Γ cp.firstStep :=
    (nine_four_auxiliary_core_geometry ctx hb d data.actor data.actor_mem).1
  have hR0F : R0 ≤ F := le_sup_left
  have hT0R0 : T0 ≤ R0 := nine_four_actor_closure_le_core_intersection ctx hb
    data.remote data.distance data.actor ⟨data.actor_mem,data.actor_centralizes⟩
    data.conjugator data.conjugator_mem hremote hne
  have hTcentral : T0 ≤ Subgroup.centralizer (A : Set G) :=
    (nine_four_actor_closure_action ctx.toLocalContext data.remote data.actor
      data.actor_centralizes data.conjugator hremote).1.trans
        (Subgroup.centralizer_le data.subgroup_le)
  have hTnormQ : T0 ≤ Subgroup.normalizer Qn :=
    (hT0R0.trans (hR0F.trans hFP)).trans (stabilizer_le_normalizer_q Γ cp.firstStep)
  have hRcover : R0 ≤ D0 ⊔ T0 := by
    intro r hr
    have hrSup : r ∈ Qn ⊔ T0 := by simpa only [sup_comm] using hcover hr
    have hrProd : r ∈ (Qn : Set G)*(T0 : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Qn T0 hTnormQ]
      exact hrSup
    obtain ⟨q,hq,t,ht,rfl⟩ := hrProd
    have hqR : q ∈ R0 := by
      have hh := R0.mul_mem hr (R0.inv_mem (hT0R0 ht))
      simpa only [mul_inv_cancel_right] using hh
    exact (D0 ⊔ T0).mul_mem (Subgroup.mem_sup_left ⟨hqR,hq⟩) (Subgroup.mem_sup_right ht)
  by_contra hnontrivial
  have hJne : J ≠ ⊥ := by
    intro hJbot
    have hDcentral : D0 ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJbot)
    exact hnontrivial (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (hRcover.trans (sup_le hDcentral hTcentral))))
  have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
  have hQnEdge : Qn ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers
  have hnextMem : cp.firstStep ∈ Neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    hnextMem hremote
  have hdOrbit : IsConjugateVertex Γ cp.firstStep d := ⟨mover,hmover⟩
  have hdData := nine_next_center_commutator_and_kernel ctx hb d hdOrbit
  have hJZd : J ≤ Zd :=
    (Subgroup.commutator_mono data.subgroup_le (inf_le_left.trans inf_le_right)).trans_eq hdData.2.1
  have hJcard : Nat.card J = 2 := by
    have hdvd : Nat.card J ∣ 2 := hdData.1 ▸ Subgroup.card_dvd_of_le hJZd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exact (hJne (Subgroup.card_eq_one.mp hone)).elim
    · exact htwo
  have hJZdEq : J = Zd := Subgroup.eq_of_le_of_card_ge hJZd (by rw [hJcard,hdData.1])
  have hsplit := nine_three_center_split ctx hb ⟨1,Γ.act_one _⟩ cp.firstStep_adj
    ((mem_neighborhood_iff_adjacent Γ).mp hremote) hne.symm
  have hZaJoin : Za = J ⊔ Zn := by
    rw [hJZdEq,sup_comm]
    exact hsplit.1
  have hZaQa : Za ≤ Qa :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hnextMem).trans
      ((omegaOneCenter_le_centerAmbient Qa).trans (Subgroup.map_subtype_le _))
  have hZnZa : Zn ≤ Za := (show Zn ≤ Zn ⊔ Zd from le_sup_left).trans_eq hsplit.1.symm
  have hZdZa : Zd ≤ Za := (show Zd ≤ Zn ⊔ Zd from le_sup_right).trans_eq hsplit.1.symm
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hAQa : A ≤ Qa := data.subgroup_le.trans
    ((nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a))
  have hPZn := stabilizer_le_normalizer_z Γ cp.firstStep
  have hAZn : A ≤ Subgroup.normalizer Zn := hAQa.trans (hQaEdge.trans (inf_le_right.trans hPZn))
  have hDZn : D0 ≤ Subgroup.normalizer Zn := inf_le_left.trans (hR0F.trans (hFP.trans hPZn))
  have hEF : E ≤ F := twoResidualIn_le F
  have hEZn : E ≤ Subgroup.normalizer Zn := hEF.trans (hFP.trans hPZn)
  let K := F ⊓ Qn
  have hKF : K ≤ F := inf_le_left
  have hKnormal : (K.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKF).mpr
      ((le_inf F.le_normalizer (hFP.trans (stabilizer_le_normalizer_q Γ cp.firstStep))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hQntwo : IsPGroup 2 Qn := by
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt Γ cp.firstStep)).map _
  have hKcore : K ≤ twoCoreIn F := by
    have hnative : K.subgroupOf F ≤ pCore 2 F :=
      le_sSup ⟨hKnormal,((hQntwo.to_le (show K ≤ Qn from inf_le_right)).comap_subtype)⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hKF]
    exact Subgroup.map_mono hnative
  have hDcore : D0 ≤ twoCoreIn F :=
    (le_inf (inf_le_left.trans hR0F) inf_le_right).trans hKcore
  have hDE : ⁅D0,E⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hDcore).trans (residual_commutator_core_le F)
  have hAE : ⁅A,E⁆ ≤ Vn :=
    (Subgroup.commutator_mono le_sup_left hEF).trans
      (nine_four_auxiliary_normalization ctx hb d hremote data.actor data.actor_mem
        A data.subgroup_le data.commutator_le).2
  have hVnD : ⁅Vn,D0⁆ ≤ Zn :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).2.1
  have hJE : ⁅J,E⁆ ≤ Zn := by
    apply Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer hAZn hDZn hEZn
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl hDE).trans hcentral
    · have hEA : ⁅E,A⁆ ≤ Vn := by simpa only [Subgroup.commutator_comm] using hAE
      exact (Subgroup.commutator_mono hEA le_rfl).trans hVnD
  have hZaE : ⁅Za,E⁆ ≤ Zn := by
    rw [hZaJoin]
    exact sup_commutator_le (Subgroup.normalizer Zn) J Zn E Zn le_rfl
      (hJZd.trans (hZdZa.trans (hZaQa.trans (hQaEdge.trans (inf_le_right.trans hPZn)))))
      Zn.le_normalizer hJE (Subgroup.le_normalizer_iff_commutator_le_left.mp hEZn)
  have hEZa : E ≤ Subgroup.normalizer Za :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hZaE.trans hZnZa)
  have hRZa : R0 ≤ Subgroup.normalizer Za :=
    inf_le_left.trans (hQaEdge.trans (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a)))
  have hKZa : K ≤ Subgroup.normalizer Za :=
    inf_le_right.trans (hQnEdge.trans (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a)))
  have hFZa : F ≤ Subgroup.normalizer Za :=
    hgeneration.le.trans (sup_le (sup_le hEZa hRZa) hKZa)
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hPZa : GAt Γ cp.firstStep ≤ Subgroup.normalizer Za := hgen.symm.le.trans
    (sup_le (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a))
      (le_sup_right.trans hFZa))
  have hEP : EAt Γ cp.firstStep ≤ GAt Γ cp.firstStep := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hVZa : Vn ≤ Za := nine_five_neighbor_module_le_of_residual_normalizes
    ctx.toLocalContext cp.a cp.firstStep cp.firstStep_adj Za le_rfl (hEP.trans hPZa)
  have hZaVd : Za ≤ VAt Γ d := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote))
  have hIeq : Vn ⊓ VAt Γ d = Vn := inf_eq_left.mpr (hVZa.trans hZaVd)
  change 4 * Nat.card (Vn ⊓ VAt Γ d : Subgroup G) ≤ Nat.card Vn at hlarge
  rw [hIeq] at hlarge
  have hpositive : 0 < Nat.card Vn := Nat.card_pos
  omega

end Stellmacher.SectionNine
