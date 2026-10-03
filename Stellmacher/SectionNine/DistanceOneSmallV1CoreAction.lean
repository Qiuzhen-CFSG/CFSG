module
public import Stellmacher.SectionNine.DistanceOneV1ActionClassification
public import Theory.GroupAction.QuotientConjugationFullRankLayer
public import Theory.GroupTheory.Commutator.ActionTriviality
/-!
# The small V₁ quotient cases centralize the initial core layer

In an ambient critical-length-one configuration, let U satisfy the
maximal-V₁ commutator, Sylow-normality, and initial-center action bounds.
If |U| ≤ 16 |Z_terminal|, then [Q_initial,U] ≤ Z_initial. This is the
small-case elimination in the chief-factor argument; no core equality or
faithful initial-center classification is assumed.

The actual (1.3) packet gives quotient orders four, sixteen, or sixty-four.
The size bound excludes sixty-four. In each remaining case its selected
involution has fixed subgroup and action commutator of the same order;
rank-nullity identifies these subgroups. The initial core commutes with
the selected involution and fixes its action commutators, because the
involution lies in the initial center and U normalizes that center.
The full-rank quotient-conjugation lemma therefore places the initial
core's commutators with U in the initial center. The terminal center lies
there by (7.5) and the Sylow-center definition, so the quotient bound pulls
back to the stated ambient subgroup bound.

Source: Stellmacher, Journal of Algebra 190 (1997), p.47, the sentence
following the (1.3) dichotomy in (9.1) that a noncentral core-action branch
forces |V₁/Z_(alpha+1)| = 64.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
private theorem full_rank_of_small_classification
    (W : Type u) [Group W] [Finite W] [Nontrivial W] [IsElementaryAbelian 2 W]
    (F : Subgroup (MulAut W)) (x : MulAut W) (hx : _root_.IsInvolution x)
    (hfull : commutatorAction F W = ⊤)
    (hclass : SectionOne.LemmaOneThreeConclusion (MulAut W) W x F)
    (hsmall : Nat.card W ≤ 16) :
    Nat.card W = Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) W) ^ 2 := by
  have hcardF : Nat.card (commutatorAction F W) = Nat.card W := by
    rw [hfull, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv]
  cases hclass with
  | cyclicThree hcard _ =>
    have hW : Nat.card W = 4 := hcardF.symm.trans hcard
    have hX : Nat.card (Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
    have hne : commutatorAction (Subgroup.zpowers x) W ≠ ⊥ := by
      intro hbot
      have hh := actsTrivially_of_commutatorAction_eq_bot hbot
      apply hx.1
      ext w
      exact hh ⟨x,Subgroup.mem_zpowers x⟩ w
    have hline := four_element_action_fixed_commutator_card_two hX hW hne
    rw [hW,hline.1]
    norm_num
  | small hcard hfixed _ =>
    have hW : Nat.card W = 16 := hcardF.symm.trans hcard
    have hC : Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) W) = 4 := by omega
    rw [hW,hC]
    norm_num
  | extraspecial hcard _ _ _ _ =>
    have hW : Nat.card W = 64 := hcardF.symm.trans hcard
    omega
public theorem distance_one_small_v1_core_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (U : Subgroup G)
    (hUQ : U ≤ q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a' ≤ U)
    (hUQc : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = U)
    (hUT : U ≤ T) (hUn : (U.subgroupOf T).Normal)
    (hlow : Nat.card (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G)
      < Nat.card U)
    (hupper : Nat.card U ≤ 4 * Nat.card
      (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G))
    (hsmall : Nat.card U ≤ 16 * Nat.card (z ctx.Γ ctx.criticalPath.a')) :
    ⁅q ctx.Γ ctx.criticalPath.a,U⁆ ≤ z ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a'
  let Za := z Γ cp.a
  let Z := z Γ cp.a'
  let Qa := q Γ cp.a
  obtain ⟨hN,hW,hWne,hPU,ρ,hρ,hker,hfull,x,hx,hxi,hxQ,hxi',hFx,hclass⟩ :=
    distance_one_v1_action_classification ctx hb U hUQ hZU hUQc hUE hUT hUn hlow hupper
  let _ := hN
  let _ := hW
  let _ := hWne
  let W := U ⧸ Z.subgroupOf U
  have hWsmall : Nat.card W ≤ 16 := by
    have hcount := (Z.subgroupOf U).card_mul_index
    rw [Subgroup.index_eq_card] at hcount
    have hZcard : Nat.card (Z.subgroupOf U) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
    rw [hZcard] at hcount
    change Nat.card Z * Nat.card W = Nat.card U at hcount
    rw [← hcount, mul_comm 16] at hsmall
    exact Nat.le_of_mul_le_mul_left hsmall Nat.card_pos
  have hrank := full_rank_of_small_classification W _ (ρ x) hxi' hfull hclass hWsmall
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hTQa := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hTP : T ≤ P := by
    change T ≤ stabilizer Γ cp.a'
    rw [← hstep]
    exact (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hZa : Za ≤ omegaOneCenter Qa :=
    (lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.a' hneighbor
  have hQA : Qa ≤ Subgroup.centralizer (Za:Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hZa.trans ((omegaOneCenter_le_centerAmbient Qa).trans (centerAmbient_le_centralizer Qa)))
  have hUA : U ≤ Subgroup.normalizer (Za:Set G) :=
    (hUT.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1).trans
      (stabilizer_le_normalizer_z Γ cp.a)
  have hZA : Z ≤ Za := by
    have h75 := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.1
    rw [hstep] at h75
    rw [show Z = omegaOneCenter T from h75]
    obtain ⟨_, R, hR⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
    change omegaOneCenter T ≤ z Γ cp.a
    rw [z, Γ.zAt_def]
    exact le_sSup ⟨R, congrArg omegaOneCenter hR.symm⟩
  exact Subgroup.commutator_le_of_quotient_full_rank_involution P U Z Za Qa hPU hN hZA hUA (hTQa.trans hTP) hQA ρ hρ x hx hW hxi' hrank
end Stellmacher.SectionNine
