module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ExceptionalSixExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenWeightTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Parabolics
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock
-- Intentional internal extension of the selected-component proof: only its
-- MS normalizer-escape argument and central seed lemma are reused privately.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeInput
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalRows

/-!
# Small blocks in the original C-component branch

The extra hypothesis K ∈ C(G₁) in 15.1.20(2b) supplies C.2.7 on KQ₁
using the original radical and characteristic-normalizer control. The FF
quotient marking gives Q₁-normalization in the alternating and G₂ rows;
C.2.4 gives it in the binary-three row, whose quotient order excludes
rank-one blocks. The same M_Z supplies the odd-index MS witness.

Whole-block reconstruction and the original offender exclusions then apply
to these K without changing the selected L or making a new source record.
The A₇ row retains its actual weight-two vector and equivariant action.
The A₆ argument retains the full central cover until the original cubic
block exclusion. Its independently owned reconstruction input stays explicit.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095, and C.2.7.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- C.2.7 on an actual C-component K of the original G₁. -/
theorem PreExclusionSource.localComponent_input_of_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hfit : generalizedFitting K = pCore 2 K)
    (hnL : d.Q1 ≤ normalizer (K : Set G)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K := by
  let := h.elementary
  have hQM : d.Q1 ≤ d.MZ := d.Q1_le_MZ
  have hQG : d.Q1 ≤ d.G1 := hQM.trans inf_le_left
  have hMnorm : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  let : (d.Q1.subgroupOf d.MZ).Normal := normal_subgroupOf_of_le_normalizer hMnorm
  have hclosure :
      (normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype = d.Q1 := by
    rw [normalClosure_eq_self, map_subgroupOf_eq_of_le hQM]
  have hsy : Chapter1.IsSylowIn 2 d.Q1
      ((normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype) := by
    rw [hclosure]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 d.MZ, le_rfl,
      fun U _ hQU hUQ => le_antisymm hUQ hQU⟩
  exact ⟨⟨caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)),
    hQG, inf_le_left,
    caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left s.core_nontrivial s.core_normalizer,
    caseI_intrinsic_characteristic_control d.G1 Mc d.Q1 hQG s.characteristic_control, hsy⟩,
    hK, hq, hfit, hout, hnL⟩

/-- The same original M_Z gives MS2(a) for each actual C-component. -/
theorem localComponent_msOddIndexRadical (d : CaseIComponentData T M Mc V)
    {K : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K)
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    ChapterC.MSOddIndexRadical (d.Q1.subgroupOf d.G1) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : d.S ≤ d.MZ := le_inf d.S_le_G1 (d.S_le_T.trans hTMc)
  obtain ⟨P,hP⟩ := hs
  apply msOddIndexRadical_of_first_core hi d.MZ inf_le_left le_rfl P
  · intro x hx
    exact hSM (hP ▸ mem_map_of_mem d.G1.subtype hx)
  · rfl

/-- The original A₇ FF row gives the ordinary whole block and its original
weight-two stabilizer for every local member which is a C-component of G₁. -/
theorem PreExclusionSource.localComponent_seven
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock K 7 ∧
      ∃ t : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
        (∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k)) ∧
        ∃ E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
          (∀ k u, E (blockConjugate K k u) =
            BinaryPermutation.SevenMarkedAction.coreAction
              (t (QuotientGroup.mk' (pCore 2 K) k)).val (E u)) ∧
          ∃ u : blockU K, BinarySevenCode.weight (E u).toAdd.val = 2 ∧
            ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G) ∧
            d.MZ ⊓ K = K ⊓ centralizer ({((u : K) : G)} : Set G) ∧
            IsCoatom ((d.MZ ⊓ K).subgroupOf K) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  have hn := d.localFamily_alternating_central_normalizes hG h hK hq (by decide)
    (a.alternating_coreCenterEquiv hq (by decide) e)
  have hQS := d.catalogue_radical_le_sylow s.centralizer_sylow hu
  have hi := s.localComponent_input_of_normalizes (h := h) hG hc hq hout hf (hQS.trans hn)
  obtain ⟨hb,t,ht⟩ := d.localFamily_seven_marked_blocks hG hempty hM hJ hu h hK hq hout hf e
  have hb := hb.resolve_right (d.localFamily_not_exceptional_seven h hM.1.2 hu hK hi hn hQS)
  exact ⟨hb,t,ht,d.localFamily_seven_weight_two h hM.1.2 hu hK hi hb t⟩

/-- The G₂ quotient gives the whole original block, with no new source
record for K and with its actual core-to-FF marking preserved. -/
theorem PreExclusionSource.localComponent_g2_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock K ∧
      ∃ t : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)),
        ∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let t := a.g2Derived_coreEquiv hq e
  have hn := d.localFamily_g2_normalizes hG h hK hq t
  have hi := s.localComponent_input_of_normalizes (h := h) hG hc hq hout hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hn)
  exact ⟨Chapter14.Section06.g2_block_from_c27 g2Reconstruction_knownSimple hi
    (d.localComponent_msOddIndexRadical hi s.centralizer_sylow hu) t,t,fun _ => rfl⟩

/-- Both six-point covering outcomes are handled on the original KQ₁.
The exceptional cubic outcome contradicts its actual C.2.7 offender. -/
theorem PreExclusionSource.localComponent_six_block_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (d.normalizerImage K ⧸ center (d.normalizerImage K)) ≃* alternatingGroup (Fin 6)) :
    IsAlternatingBlock K 6 ∧
      ∃ t : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6),
        ∀ k : K, t (QuotientGroup.mk' (centralPreimage (pCore 2 K)) k) =
          e (QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K k)) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let t := (a.coreCenterQuotientEquiv hq).trans e
  have hn := d.localFamily_alternating_central_normalizes hG h hK hq (by decide) t
  have hQS := d.catalogue_radical_le_sylow s.centralizer_sylow hu
  have hi := s.localComponent_input_of_normalizes (h := h) hG hc hq hout hf (hQS.trans hn)
  let es := t.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
    (F := ZMod 2) (by simp)).symm
  have hm := Chapter14.Section06.smallMSPair_from_c27 hi
    (d.localComponent_msOddIndexRadical hi s.centralizer_sylow hu) (Or.inr (Or.inl ⟨es⟩))
  have r := ha G K d.Q1 hm es
  have hs := hm.short_of_core r.elementary r.central hq r.irreducible
  have hb : IsAlternatingBlock K 6 := by
    rcases r.model with hm | ⟨hz,hU,hC⟩
    · exact ⟨by decide,hs,hm⟩
    · exact (d.localFamily_not_exceptionalSix_of_input h hM.1.2 hu hK hQS hi
        ⟨hs,hq,hz,⟨(centralPreimageQuotientEquiv (pCore 2 K)).symm.trans t⟩,hU,hC⟩).elim
  exact ⟨hb,t,fun k => congrArg e (a.coreCenterQuotientEquiv_mk hq k)⟩
private theorem localComponent_binaryThree_from_original
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hQne : d.Q1 ≠ ⊥) (hnM : (T : Subgroup G) ≤ normalizer (d.MZ : Set G))
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    {K : Subgroup G} (hKG : K ≤ d.G1)
    (hSL : Chapter1.IsSylowIn 2 (d.S ⊓ K) K)
    (hn : d.Q1 ≤ normalizer (K : Set G))
    (hm : SmallMSPair KnownSimple.IsKnownSimple K d.Q1)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock K 1 := by
  let S0 := (d.S ⊓ K) ⊔ d.Q1
  have hQS := d.catalogue_radical_le_sylow hs hu
  have hS0S : S0 ≤ d.S := sup_le inf_le_left hQS
  have hS0N : S0 ≤ normalizer (K : Set G) :=
    sup_le (inf_le_right.trans K.le_normalizer) hn
  have hgen : K ⊔ S0 = K ⊔ d.Q1 := by
    rw [←sup_assoc,sup_eq_left.mpr (show (d.S ⊓ K) ≤ K from inf_le_right)]
  obtain ⟨P,hP⟩ := hSL
  have hSyl : Chapter1.IsSylowIn 2 S0 (K ⊔ d.Q1) := by
    rw [←hgen]
    exact (T.isPGroup'.to_le (hS0S.trans d.S_le_T)).exists_sylow_sup_of_coprime_index
      K S0 hS0N (P : Subgroup K) P.not_dvd_index (hP ▸ le_sup_left)
  have hZQ := d.central_seed_le_radical hG h hTM hu hQne hnM
  have hZomega : centralInvolutions T ≤ FullSieve.SourceInterface.omegaCenterIn S0 := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨mem_sup_right (hZQ hz),
      ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.1,
      fun x hx => centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T (hS0S hx))⟩
  apply (binaryThree_block_or_normalizer_escape hm e hSyl le_sup_right).resolve_right
  intro hesc
  apply hesc
  intro l hl
  have hMc : l ∈ Mc := centralizer_le_partner T hu (centralizer_le hZomega hl.2)
  exact (d.MZ.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ)))
      ⟨hKG hl.1,hMc⟩

/-- The binary-three whole-block theorem in the source's actual C-component
branch, with the original quotient and core-to-FF marking. -/
theorem PreExclusionSource.localComponent_binaryThree_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* Matrix.PSL3Two.SL) :
    IsSL3EvenBlock K 1 ∧
      ∃ t : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL,
        ∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let t := a.binaryThree_coreEquiv hq e
  have hn := (d.constrained_component_rankOne_or_normalizes_of_radical_control h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    hc hq hf hout).resolve_left (binaryThree_not_rankOne t)
  have hi := s.localComponent_input_of_normalizes (h := h) hG hc hq hout hf hn
  have hm := Chapter14.Section06.smallMSPair_from_c27 hi
    (d.localComponent_msOddIndexRadical hi s.centralizer_sylow hu) (binaryThree_smallQuotient t)
  have hSK := ComponentModels.source20_sylow_intersection hK.2
  exact ⟨d.localComponent_binaryThree_from_original hG h hM.1.2 hu s.core_nontrivial
    s.sylow_normalizes_MZ s.centralizer_sylow hK.1 hSK hn hm t,t,
    a.binaryThree_coreEquiv_mk hq e⟩

/-- Exhaustive whole-block reconstruction in the additional C-component
branch of 15.1.20(2b), alongside the already proved group/intersection rows.
The original natural escape is excluded at either source prime. -/
theorem PreExclusionSource.localComponent_block_rows
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K ∧
      (IsAlternatingBlock K 5 ∨ IsAlternatingBlock K 7 ∨ IsSL3EvenBlock K 1 ∨
        IsAlternatingBlock K 6 ∨ ChapterC.IsG2TwoBlock K ∨
        ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨hm,hr⟩ := s.localFamily_constrained_source_rows (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf
  refine ⟨hm,hr,?_⟩
  have rankOne (F : ChapterB.QuasisimpleSource.BinaryField)
      (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
      IsAlternatingBlock K 5 := by
    rcases d.localFamily_rankOne_block hG hempty hM hJ hu h hK hq hout hf F.Carrier e with
      ⟨n,hb⟩ | hb
    · exact (hout (s.localFamily_linearTwo_le_MZ (h := h) hp
        hG hempty hM hJ hu hne hmany hfull hres hK hq hb)).elim
    · exact hb
  have linear {n : ℕ} (hn : n = 4 ∨ n = 5)
      (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    obtain ⟨t,_,_,_⟩ := d.localFamily_binary_linear_marked_parabolics
      hG hempty hM hJ hu h hK hq hout hf hn e
    exact ⟨n,hn,⟨t⟩⟩
  cases d.localFamily_reduced_ff_model hG hempty hM hJ hu h hK hq hout hf with
  | linearTwo F e => exact Or.inl (rankOne F e)
  | linearThree e =>
    exact Or.inr (Or.inr (Or.inl ((s.localComponent_binaryThree_block (h := h)
      hG hempty hM hJ hu hK hc hq hout hf e).1)))
  | g2DerivedTwo e =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((s.localComponent_g2_block (h := h) hG hempty hM hJ hu hK hc hq hout hf e).1)))))
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact Or.inl (rankOne ChapterB.QuasisimpleSource.BinaryField.four
        (e.trans fiveLinearEquiv))
    · let ec := (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
        ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)))).trans
            QuotientGroup.quotientBot)
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ((s.localComponent_six_block_of_reconstruction (h := h) ha
          hG hempty hM hJ hu hK hc hq hout hf ec).1))))
    · exact Or.inr (Or.inl ((s.localComponent_seven (h := h)
        hG hempty hM hJ hu hK hc hq hout hf e).1))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (linear (Or.inl rfl) (e.trans
        (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm)))))))
  | linearFiveTwo e =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (linear (Or.inr rfl) e)))))
  | tripleSix _ e =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ((s.localComponent_six_block_of_reconstruction (h := h) ha
        hG hempty hM hJ hu hK hc hq hout hf e).1))))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original marker supplies the group/intersection rows for every eligible
local K and the whole-block refinement precisely for its actual C-components.
All groups, quotient maps and original source hypotheses are retained. -/
theorem PreparedChosenModule.source_preExclusion_localComponent_blocks
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedSourceRows d K ∧
          (K ∈ Chapter1.cComponentsIn d.G1 →
            IsAlternatingBlock K 5 ∨ IsAlternatingBlock K 7 ∨ IsSL3EvenBlock K 1 ∨
              IsAlternatingBlock K 6 ∨ ChapterC.IsG2TwoBlock K ∨
              ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
                Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  obtain ⟨hm,hrows⟩ := s.localFamily_constrained_source_rows (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf
  exact ⟨hm,hrows,fun hc => (s.localComponent_block_rows (h := h) hp ha
    hG hempty hM hJ hu hne hmany hfull hres hK hc hq hout hf).2.2⟩

end CFSG.Quasithin.Chapter15.Section01
