module
public import Stellmacher.SectionFiveToSeven.SixFourNormalContainerTransfer
public import Stellmacher.BaumannFullCommutatorCoreNormalizer
public import Stellmacher.SectionFiveToSeven.Result5_4
public import Stellmacher.SectionFiveToSeven.SixFourBarredAction
public import Stellmacher.SectionThree.LemmaThreeSeven
/-!
# The repeated (6.4) transfer from an invariant nonzero seed

In the central branch of Hypothesis Two, let K≤P₂ satisfy K=[K,B(S)].
Write R=O²(P₁) and L=R K B(S). If L normalizes a nonzero subgroup W≤S
contained in L, then K centralizes the full Section Six module. There is
no action-critical subgroup hypothesis and no selected-factor assumption.

The invariant two-subgroup W makes O₂(L) nontrivial. The asymmetric
Baumann core-normalizer lemma shows that L normalizes S∩O₂(L), and the
global Sylow form of (5.4) places Ω₁Z(S) in that intersection. The (5.2)
subnormal transfer and normal-container argument then make K centralize
the normal closure of Ω₁Z(S) in its two-local normalizer. Since P₁=R S,
this container includes the full Section Six module.

This isolates the common repeated argument in Stellmacher (6.4), Journal
of Algebra 190 (1997), printed p.32. In the native centralizing branch of
(9.1), p.47, the actual odd fixed complement supplies W; the original
canonical application supplies its selected four-element module.
Source: refs/files/stellmacher-n-group.pdf. All groups remain in the
original ambient Hypothesis Two context.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u
private theorem normal_residual {H : Type*} [Group H] (P : Subgroup H) :
    ((twoResidualAmbient P).subgroupOf P).Normal := by
  change (((twoResidualSubgroup P).map P.subtype).subgroupOf P).Normal
  rw [subgroupOf_map_subtype_eq]
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal fun N => Subgroup.normal_iInf_normal fun hN => hN.1

public theorem sixFour_invariant_seed_transfer {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥)
    (K : Subgroup H) (hKP : K ≤ P2) (hKB : K = ⁅K,baumannIn S⁆)
    (W : Subgroup H) (hWne : W ≠ ⊥) (hWS : W ≤ S)
    (hWL : W ≤ twoResidualAmbient P1 ⊔ K ⊔ baumannIn S)
    (hLW : twoResidualAmbient P1 ⊔ K ⊔ baumannIn S ≤ Subgroup.normalizer (W : Set H)) :
    ⁅sectionSixV S P1,K⁆ = ⊥ := by
  let R := twoResidualAmbient P1
  let B := baumannIn S
  let L := R ⊔ K ⊔ B
  have hZP : omegaOneCenter S ≤ P2 :=
    (Subgroup.map_subtype_le _).trans h.fiveOne.P2_mem.1.2.1.1
  have hZn : NormalIn (omegaOneCenter S) P2 := ⟨hZP,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _))⟩
  have hcase : S = (S0 : Subgroup H) ∧ P2 ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter S : Set H)) S := by
    cases h.fiveOne.alternative with
    | a _ _ hn => exact (hn hZn).elim
    | b hS hstar => exact ⟨hS,hstar⟩
    | c _ _ _ _ hn _ _ _ _ _ _ _ _ => exact (hn hZn).elim
  obtain ⟨hS,hstar⟩ := hcase
  have hred := five_two_initial_reductions S0 P2 K (hS ▸ hstar) hKP
    (hS ▸ h.local_B) (hS ▸ hKB)
  have hKcoreS : twoCoreAmbient K ≤ S := by
    have ha := pCoreAmbient_mono_of_isSubnormalIn K (twoResidualAmbient P2) 2
      hred.2.2.1.1 hred.2.2.1.2
    have hb := pCoreAmbient_mono_of_isSubnormalIn (twoResidualAmbient P2) P2 2
      (Subgroup.map_subtype_le _) (normal_residual P2).isSubnormal
    obtain ⟨_,T,hT⟩ := h.fiveOne.P2_mem.1.2.1
    exact (ha.trans hb).trans (hT ▸ Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P2)).le_sylow_of_normal T))
  have hRcoreS : twoCoreAmbient R ≤ S := by
    have hb := pCoreAmbient_mono_of_isSubnormalIn R P1 2
      (Subgroup.map_subtype_le _) (normal_residual P1).isSubnormal
    obtain ⟨_,T,hT⟩ := h.fiveOne.P1_mem.1.2.1
    exact hb.trans (hT ▸ Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P1)).le_sylow_of_normal T))
  have hWp : IsPGroup 2 W := (hS ▸ S0.isPGroup').to_le hWS
  have hWcore : W ≤ twoCoreAmbient L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWL]
    exact Subgroup.map_mono (le_sSup ⟨
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr hLW,
      hWp.comap_of_injective L.subtype L.subtype_injective⟩)
  have hLcore : twoCoreIn L ≠ ⊥ := fun he => hWne
    (bot_unique (hWcore.trans_eq he))
  have hLQ : L ≤ Subgroup.normalizer (twoCoreAmbient L : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp (by
      rw [subgroupOf_map_subtype_eq]
      infer_instance)
  have hSR : S ≤ Subgroup.normalizer (R : Set H) :=
    h.fiveOne.P1_mem.1.2.1.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (normal_residual P1))
  have hLN : L ≤ Subgroup.normalizer ((S ⊓ twoCoreAmbient L : Subgroup H) : Set H) := by
    subst S
    exact baumann_pair_normalizes_core_intersection S0 R K (twoCoreAmbient L)
      ((pCore_isPGroup (p := 2) (G := L)).map L.subtype)
      ((sup_le (le_sup_left.trans le_sup_left) le_sup_right).trans hLQ)
      ((sup_le (le_sup_right.trans le_sup_left) le_sup_right).trans hLQ)
      hSR hKB hRcoreS hKcoreS
  have hZcore := omegaOneCenter_le_core_of_globalSylow S0 S P1 P2 h hS L
    le_sup_right hLcore hLN
  let Q := S ⊓ twoCoreAmbient L
  let U := Subgroup.normalizer (Q : Set H)
  have hZQ : omegaOneCenter S ≤ Q := le_inf
    (Subgroup.map_subtype_le _) hZcore
  have hQne : Q ≠ ⊥ := fun he => hWne (bot_unique ((le_inf hWS hWcore).trans_eq he))
  have hQU : Q ≤ U := Subgroup.le_normalizer
  have hQp : IsPGroup 2 Q :=
    ((pCore_isPGroup (p := 2) (G := L)).map L.subtype).to_le inf_le_right
  have hU : IsTwoLocal U := ⟨Q,hQne,hQp,rfl⟩
  have hKL : K ≤ L := le_sup_right.trans le_sup_left
  have hBU : B ⊔ K ≤ U := (sup_le le_sup_right hKL).trans hLN
  have hKsub := lemma_five_two S0 (omegaOneCenter (S0 : Subgroup H))
    (baumannIn (S0 : Subgroup H))
    (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup H) : Set H))
    P2 K rfl rfl rfl (hS ▸ hstar) hKP (hS ▸ h.local_B) (hS ▸ hKB)
    U hU (hS ▸ hBU)
  have hKcoreL : twoCoreAmbient K ≤ twoCoreAmbient L :=
    pCoreAmbient_mono_of_isSubnormalIn K L 2 hKL
      (hKsub.2.comap (Subgroup.inclusion hLN))
  have hKQ : twoCoreAmbient K ≤ Q := le_inf hKcoreS hKcoreL
  have htransfer := sixFour_normal_container_transfer h hcomm K hKP hKB
    U hU hBU Q hQU inf_le_left Subgroup.normal_in_normalizer hZQ hKQ
  let A0 := Subgroup.normalClosure ((omegaOneCenter S).subgroupOf U : Set U)
  let A := A0.map U.subtype
  have hZA : omegaOneCenter S ≤ A := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hZQ.trans hQU)]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hAn : (A.subgroupOf U).Normal := by
    rw [show A = A0.map U.subtype from rfl,subgroupOf_map_subtype_eq]
    exact Subgroup.normalClosure_normal
  have hUA : U ≤ Subgroup.normalizer (A : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hAn
  have hRA : R ≤ Subgroup.normalizer (A : Set H) :=
    (le_sup_left.trans le_sup_left).trans (hLN.trans hUA)
  have hVA : sectionSixV S P1 ≤ A := by
    rw [sectionSixV,conjugateClosure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨p,z,rfl⟩
    let SP := sectionSixSylow h
    let Rn := twoResidualSubgroup P1
    let _ : Rn.Normal := by
      unfold Rn twoResidualSubgroup
      rw [sInf_eq_iInf]
      exact Subgroup.normal_iInf_normal fun N => Subgroup.normal_iInf_normal fun hN => hN.1
    have hgen : Rn ⊔ (SP : Subgroup P1) = ⊤ := by
      apply Subgroup.map_injective P1.subtype_injective
      rw [Subgroup.map_sup,← MonoidHom.range_eq_map,Subgroup.range_subtype,
        (sectionSix_barred_action_setup h).sylow_image]
      exact SectionThree.twoResidual_sup_sylowImage h.fiveOne.P1_mem.1.2.1.2
    have hp : p ∈ Rn ⊔ (SP : Subgroup P1) := by rw [hgen]; trivial
    obtain ⟨r,hr,t,ht,he⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    have htS : (t : H) ∈ S := (sectionSix_barred_action_setup h).sylow_image.le
      (Subgroup.mem_map_of_mem P1.subtype ht)
    have htz : (t : H) * (z : H) * (t : H)⁻¹ = z := by
      have hc := (mem_omegaOneCenterAmbient_iff S (z : H)).mp z.property |>.2.2 t htS
      rw [hc,mul_assoc,mul_inv_cancel,mul_one]
    have hrR : (r : H) ∈ R := Subgroup.mem_map_of_mem P1.subtype hr
    have hconj := (Subgroup.mem_normalizer_iff.mp (hRA hrR) (z : H)).mp (hZA z.property)
    have heH := congrArg P1.subtype he
    change (r : H) * (t : H) = (p : H) at heH
    rw [← heH,mul_inv_rev]
    have heq : ((r : H) * t) * z * ((t : H)⁻¹ * (r : H)⁻¹) =
        (r : H) * ((t : H) * z * (t : H)⁻¹) * (r : H)⁻¹ := by group
    rw [heq,htz]
    exact hconj
  exact bot_unique ((Subgroup.commutator_mono hVA le_rfl).trans_eq htransfer)
end Stellmacher.SectionsFiveToSeven
