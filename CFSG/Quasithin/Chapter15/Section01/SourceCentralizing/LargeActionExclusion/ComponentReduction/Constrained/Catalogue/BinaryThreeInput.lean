module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SmallAlternating
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneNormalization
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Binary-three MS input from the original FF image

For every original normalizer action, the map K/O₂(K) → K* is a perfect
central cover. The cyclic odd Sylow subgroups of SL₃(2), together with the
trivial two-core of the domain, make that literal map an isomorphism.
The equivalence agrees with the original FF marking on every element.

At the selected component, the quotient order 168 excludes both natural
L₂ blocks and permutation A₅ blocks. The proved C.2.4 alternative therefore
supplies actual Q₁-normalization, giving the C.2.7 input without assuming
characteristic two for G₁. The original M_Z supplies MS2(a), so every
small-MS hypothesis holds on the literal LQ₁. Centerlessness identifies the
star quotient through the same core-to-star map.

Both original source primes, their marker application, and both later
exchanged plane sizes are retained. This supplies the reconstruction input;
the wrong-L₃ alternatives and the natural block's parabolic and centralizer
clauses still require their source arguments. Original 15.1.14 remains
explicit in the marker application for its existing producer.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095;
C.1.31, C.1.34 and C.2.4--7, printed pp.135--137,144--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private def binaryThreeCover {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* Matrix.PSL3Two.SL) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) Matrix.PSL3Two.SL where
  toMonoidHom := e.toMonoidHom.comp a.coreToImage
  surjective := e.surjective.comp a.coreToImage_surjective
  isPerfect := hq.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact a.coreToImage_ker_central hq

/-- The original binary-three FF map identifies the literal two-core quotient. -/
noncomputable def NormalizerAction.binaryThree_coreEquiv
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* Matrix.PSL3Two.SL) :
    (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL :=
  Matrix.PSL3Two.centralCoverEquiv (binaryThreeCover a hq e) (pCore_quotient_pCore_eq_bot 2)

/-- The core equivalence preserves the prescribed original FF marking. -/
theorem NormalizerAction.binaryThree_coreEquiv_mk
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* Matrix.PSL3Two.SL) (k : K) :
    a.binaryThree_coreEquiv hq e (QuotientGroup.mk' (pCore 2 K) k) =
      e (d.toNormalizerImage K k) := by
  exact Matrix.PSL3Two.centralCoverEquiv_apply _ _ _

private theorem binaryThree_center {K : Type*} [Group K]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    center (K ⧸ pCore 2 K) = ⊥ := by
  apply bot_unique
  intro x hx
  exact e.map_eq_one_iff.mp
    (Matrix.PSL3Two.center_eq_bot.le ((centerCongr e ⟨x,hx⟩).property))

private theorem binaryThree_not_rankOne {K : Type*} [Group K]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    ¬ ((∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5) := by
  have hc : Nat.card (K ⧸ pCore 2 K) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL
  rintro (⟨n,hn,_,F,_,_,hF,_,r,⟨m⟩,_⟩ | ⟨_,_,r,⟨m⟩,_⟩)
  · rw [Nat.card_congr m.quotientIso.toEquiv,Atlas.card_sl_two,hF] at hc
    have hn3 : 3 ≤ n := by
      by_contra h
      have : n = 2 := by omega
      norm_num [this] at hc
    have hq : 8 ≤ 2^n := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn3
    have hs : 63 ≤ (2^n)^2-1 := by
      have hh : (8 : ℕ)^2 ≤ (2^n)^2 := Nat.pow_le_pow_left hq 2
      omega
    have hh := Nat.mul_le_mul hq hs
    omega
  · rw [Nat.card_congr m.quotientIso.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc

private noncomputable def binaryThree_centralEquiv {K : Type*} [Group K]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    (K ⧸ centralPreimage (pCore 2 K)) ≃* Matrix.PSL3Two.SL :=
  (centralPreimageQuotientEquiv (pCore 2 K)).trans
    (((QuotientGroup.quotientMulEquivOfEq (binaryThree_center e)).trans
      QuotientGroup.quotientBot).trans e)

private theorem binaryThree_smallQuotient {K : Type*} [Group K]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) : SmallRankTwoQuotient K := by
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  exact Or.inl ⟨(binaryThree_centralEquiv e).trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

/-- The binary-three FF row gives the literal C.2.7 and MS pair, and the
core and star markings agree with the original normalizer action. -/
theorem PreExclusionSource.constrained_binaryThree_inputs
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    ∃ hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L,
      SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ u : starImage d.L d.Q1 d.L ≃* Matrix.PSL3Two.SL,
          ∀ k : d.L, u (coreToStar hi.normalizes (QuotientGroup.mk' (pCore 2 d.L) k)) =
            e (d.toNormalizerImage d.L k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  let t := a.binaryThree_coreEquiv s.quasisimple e
  have hi := s.constrained_input_of_not_rankOne (h := h) hG hf (binaryThree_not_rankOne t)
  have hm := Chapter14.Section06.smallMSPair_from_c27 hi
    (d.constrained_msOddIndexRadical hi s.centralizer_sylow hu) (binaryThree_smallQuotient t)
  let c := d.constrained_coreStarEquiv_of_center_eq_bot hi (binaryThree_center t)
  refine ⟨hi,hm,t,a.binaryThree_coreEquiv_mk s.quasisimple e,c.symm.trans t,?_⟩
  intro k
  change t (c.symm (c (QuotientGroup.mk' (pCore 2 d.L) k))) = _
  rw [c.symm_apply_apply]
  exact a.binaryThree_coreEquiv_mk s.quasisimple e k

/-- Either exchanged plane size retains the same MS pair and both original maps. -/
theorem ExchangedSource.constrained_binaryThree_inputs
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    ∃ hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L,
      SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ u : starImage d.L d.Q1 d.L ≃* Matrix.PSL3Two.SL,
          ∀ k : d.L, u (coreToStar hi.normalizes (QuotientGroup.mk' (pCore 2 d.L) k)) =
            e (d.toNormalizerImage d.L k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  let t := a.binaryThree_coreEquiv s.quasisimple e
  have hi := s.constrained_input_of_not_rankOne hG h hf (binaryThree_not_rankOne t)
  have hm := Chapter14.Section06.smallMSPair_from_c27 hi
    (d.constrained_msOddIndexRadical hi s.centralizer_sylow hu) (binaryThree_smallQuotient t)
  let c := d.constrained_coreStarEquiv_of_center_eq_bot hi (binaryThree_center t)
  refine ⟨hi,hm,t,a.binaryThree_coreEquiv_mk s.quasisimple e,c.symm.trans t,?_⟩
  intro k
  change t (c.symm (c (QuotientGroup.mk' (pCore 2 d.L) k))) = _
  rw [c.symm_apply_apply]
  exact a.binaryThree_coreEquiv_mk s.quasisimple e k

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- Actual original-marker application at either source prime. The two-core
and star markings are both the prescribed FF map on the original L. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binaryThree_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
          ∃ hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L,
            SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
            ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
              (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) =
                e (d.toNormalizerImage d.L k)) ∧
              ∃ u : starImage d.L d.Q1 d.L ≃* Matrix.PSL3Two.SL,
                ∀ k : d.L, u (coreToStar hi.normalizes (QuotientGroup.mk' (pCore 2 d.L) k)) =
                  e (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binaryThree_inputs (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
