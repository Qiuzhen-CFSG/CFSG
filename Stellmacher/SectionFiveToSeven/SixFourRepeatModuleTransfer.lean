module
public import Stellmacher.SectionFiveToSeven.SixFourInvariantSeedTransfer
public import Stellmacher.SectionFiveToSeven.SixFourSelectedModuleContainment
public import Stellmacher.BaumannFullCommutatorCoreNormalizer
public import Stellmacher.SectionFiveToSeven.Result5_4
public import Stellmacher.SectionFiveToSeven.SixFourResidualFactorNormalizer

/-!
# The selected-factor instance of the repeated module transfer in (6.4)

Under the central branch of Hypothesis Two and nontrivial canonical barred
critical subgroup, an actual raw one-seven factor gives a four-element
module W. If K≤P₂ satisfies K=[K,B(S)] and centralizes W, then it centralizes
the full original Section Six module V.

The selected-module containment puts W in O²(P₁), while exact quotient
factor normalizers show that O²(P₁) and B(S) normalize W. The elementary
native module places W inside S, and the factor cardinality makes it
nonzero. Thus L=O²(P₁) K B(S) has an invariant nonzero seed. The general
invariant-seed transfer applies (5.4), (5.2), and the normal-container P×Q
argument to centralize the whole original V. This wrapper preserves the
canonical factor interface while sharing that group-theoretic proof with
the native centralizing branch of (9.1).

Source: Stellmacher (6.4), Journal of Algebra 190 (1997), printed p.32,
refs/files/stellmacher-n-group.pdf. No normality of V in N(W), common
Sylow for the new generators, or identity [O²(P₁),B(S)]=O²(P₁) is assumed.
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

public theorem sixFour_repeat_module_transfer {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2,omegaOneCenter S⁆ = ⊥)
    (hJ : sectionSixBarredCritical h ≠ ⊥) :
    letI := sectionSixQuotientAction h
    ∀ (D : Subgroup (SectionSixBarP1 h)),
    SectionOne.IsOneSevenFactor (V := sectionSixLocalV h) D →
    ∀ K : Subgroup H, K ≤ P2 → K = ⁅K,baumannIn S⁆ →
    let W := (commutatorAction D (sectionSixLocalV h)).map
      (P1.subtype.comp (sectionSixLocalV h).subtype)
    ⁅W,K⁆ = ⊥ → ⁅sectionSixV S P1,K⁆ = ⊥ := by
  let _ := sectionSixQuotientAction h
  intro D hD K hKP hKB W hWK
  have hRW := sixFour_residual_factor_normalizer h hJ D hD
  let R := twoResidualAmbient P1
  let B := baumannIn S
  let L := R ⊔ K ⊔ B
  have hWL : W ≤ L := by
    have hDtop : D ≤ (P1.subgroupOf P1).map (sectionSixQuotientMap h) := by
      rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)]
      exact le_top
    have hWR := sixFour_selected_module_containment h hJ D hD P1 le_rfl hDtop
    have hPR : P1 ≤ Subgroup.normalizer (R : Set H) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (normal_residual P1)
    exact (hWR.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((Subgroup.map_subtype_le _).trans
        (h.fiveOne.P1_mem.1.2.1.1.trans hPR)))).trans (le_sup_left.trans le_sup_left)
  have hLW : L ≤ Subgroup.normalizer (W : Set H) :=
    sup_le (sup_le (le_sup_left.trans hRW)
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rwa [Subgroup.commutator_comm] : ⁅K,W⁆ = ⊥)).trans
        (Subgroup.centralizer_le_normalizer _))) (le_sup_right.trans hRW)
  have hVdata := SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian
      (show SectionTwo.Hypotheses P1 from by
        obtain ⟨hsol,hchar,_⟩ := lemma_five_three S0 S P1 P2 h
        have hSPne : (sectionSixSylow h : Subgroup P1) ≠ ⊥ := by
          intro he
          apply h.fiveOne.S_nontrivial
          rw [← (sectionSix_barred_action_setup h).sylow_image,he,Subgroup.map_bot]
        have hdvd := (sectionSixSylow h).isPGroup'.card_eq_or_dvd.resolve_left
          (fun hc => hSPne (Subgroup.card_eq_one.mp hc))
        exact ⟨hsol,even_iff_two_dvd.mpr (hdvd.trans (sectionSixSylow h : Subgroup P1).card_subgroup_dvd_card),hchar⟩)
      (sectionSixSylow h)
  have hWS : W ≤ S := by
    rw [← (sectionSix_barred_action_setup h).sylow_image]
    change (commutatorAction D (sectionSixLocalV h)).map
      (P1.subtype.comp (sectionSixLocalV h).subtype) ≤ _
    rw [← Subgroup.map_map]
    exact Subgroup.map_mono ((Subgroup.map_subtype_le _).trans (hVdata.1.trans
      ((pCore_isPGroup (p := 2) (G := P1)).le_sylow_of_normal (sectionSixSylow h))))
  have hWne : W ≠ ⊥ := by
    have hcard : Nat.card W = 4 := by
      exact (Subgroup.card_map_of_injective
        (K := commutatorAction D (sectionSixLocalV h))
        (f := P1.subtype.comp (sectionSixLocalV h).subtype)
        (P1.subtype_injective.comp (sectionSixLocalV h).subtype_injective)).trans hD.2.2.1
    intro he
    rw [he,Subgroup.card_bot] at hcard
    contradiction
  exact sixFour_invariant_seed_transfer h hcomm K hKP hKB W hWne hWS hWL hLW
end Stellmacher.SectionsFiveToSeven
