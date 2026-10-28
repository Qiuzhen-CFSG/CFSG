module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.OriginalSource.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.OddModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HigmanSimsExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.RudvalisExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoTwoInner
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.MainConverse.SporadicLocal.He.Coverage
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.Automorphisms.Realization

/-!
# The original rank-two component-model contradiction

Every branch of the marked1.1.5 conclusion is evaluated on the actual
component and its centralizer quotient. The characteristic-two branch uses
the original central involution and the proved Borel action. The alternating,
odd and sporadic branches use their concrete model calculations; in the
remaining J₂ case the actual local action gives the terminal contradiction.

Source: Aschbacher--Smith, 15.3.42 and the final proof of15.3.35, pp.1138--1139.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
open ChapterA.Section05To06
open NonCharacteristicTwo NonCharacteristicTwo.SporadicSieve
variable {G : Type*} [Group G] [Finite G]

private theorem held_exclusion {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (c : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* Held.He) : False := by
  by_cases ht : componentImage I L L = ⊤
  · exact HeldExclusion.exclude_inner_of_cover c e ht
      MainConverse.SporadicLocal.he_evenCharacteristic
      MainConverse.SporadicLocal.HeCoverage.exists_sylow_two_local_cover
      Held.TwoLocalCandidates.ThreeCoreBounds.not_nine_dvd_threeCore_quotient
  · exact HeldExclusion.exclude_of_local_profile c
      (HeldExclusion.ProperExtensionProfile.componentLocal_profile_of_realization c e ht
        Held.Realization.normalizer_surjective)

/-- The actual marked catalogue has no rank-two component configuration. -/
theorem no_component_of_original_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} [(L.subgroupOf I).Normal] {z : G}
    (h : ContainmentSourceInputs d I L z) (hz : orderOf z = 2) (hzS : z ∈ d.S)
    (hcz : centralizer ({z} : Set G) = d.Mc)
    (c : ComponentSetup I L d.M d.Yplus d.S) : False := by
  let a := action_setup_of_source_inputs d h
  have hSI : d.S ≤ I := c.join_eq ▸ le_sup_right
  have hcomm : ⁅d.V₂,d.Yplus⁆ = d.V₂ := by
    rcases d.choice with he | hs
    · rw [he]
      apply le_antisymm
        (le_normalizer_iff_commutator_le_left.mp (OutsideStructure.LocalBranches.y_normalizes_plane d _))
      have hc := (residualY_fullActionCoordinateFacts d.action h.residual_image).commutator_self
        1 (Multiplicative.ofAdd (1 : ZMod 2)) (by decide)
      exact hc.ge.trans (commutator_mono le_rfl ((map_subtype_le _).trans inf_le_left))
    · exact (OutsideStructure.LocalBranches.second_choice_commutator d hs h.residual_image).2
  have hSV := OutsideStructure.LocalBranches.s_normalizes_plane d
    (Multiplicative.ofAdd (1 : ZMod 2))
  obtain ⟨α,ha,hm⟩ := h.component_structure.model_action
  have hchar (hc : Parabolics.CharacteristicTwoAction115 (L.subgroupOf I) α) : False := by
    have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
      (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans
        (show d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) from
          hu ▸ Set.mem_singleton d.Mc).2
    let zI : I := ⟨z,hSI hzS⟩
    have haction : Parabolics.Selection.SourceAction (L.subgroupOf I) (d.S.subgroupOf I) zI α := {
      mem_sylow := hzS
      involution := by simpa only [zI, Subgroup.orderOf_mk] using hz
      centralizes := by
        intro x hx
        apply Subtype.ext
        exact ((hcz.symm ▸ hTMc (show (x : G) ∈ (d.T : Subgroup G) from hx.1))
          z (Set.mem_singleton z)).symm
      action := fun x => Subtype.ext (ha x)
      alternatives := hc }
    exact Parabolics.no_characteristicTwo_of_original_action c a d.action haction hcomm hSV
  let eL := subgroupOfEquivOfLe h.component_le
  have tr (n q : ℕ) (hp : ClassicalGroup.IsPSL (L.subgroupOf I) n q) :
      ClassicalGroup.IsPSL L n q := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hp
    exact ⟨F,inferInstance,inferInstance,hF,⟨eL.symm.trans e⟩⟩
  cases hm with
  | lie hs hm hi => exact hchar (Or.inl ⟨hs,hm,hi⟩)
  | two_cover hn hz hm hi => exact hchar (Or.inr (Or.inl ⟨hn,hz,hm,hi⟩))
  | six σ hs ha => exact hchar (Or.inr (Or.inr ⟨σ,hs,ha⟩))
  | seven σ _ ha => exact AlternatingSeven.relative_alternating_action_seven_impossible c α σ ha
  | odd hm _ =>
    apply OddModels.not_odd_model c
    rcases hm with hm | ⟨p,hp,hm⟩
    · exact Or.inl (tr 3 3 hm)
    · exact Or.inr ⟨p,hp,tr 2 p hm⟩
  | sporadic name hne hm _ =>
    let q := QuotientGroup.congr (pCore 2 L) (pCore 2 (L.subgroupOf I))
      eL.symm (pCore_map_iso 2 eL.symm)
    let e := q.trans hm.some
    cases name with
    | m11 => exact MathieuExclusion.not_mathieu c .m11 (Or.inl rfl) e
    | m12 => exact MathieuExclusion.not_mathieu c .m12 (Or.inr (Or.inl rfl)) e
    | m22 => exact MathieuExclusion.not_mathieu c .m22 (Or.inr (Or.inr (Or.inl rfl))) e
    | m23 => exact MathieuExclusion.not_mathieu c .m23 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e
    | m24 => exact MathieuExclusion.not_mathieu c .m24 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) e
    | j2 =>
      obtain ⟨j⟩ := JankoTwoInner.jankoTwo_identification c e
      obtain ⟨hcard,hcentral⟩ := JankoTwoAction.local_action c a j
      exact no_component_of_local_action c a hcard hcentral
    | j3 => exact hne rfl
    | j4 => exact JankoFourExclusion.exclusion_from_selection hG d hempty hM hu hmany c e
    | hs => exact higmanSims_exclusion c e
    | he => exact held_exclusion c e
    | ru => exact RudvalisExclusion.rudvalis_exclusion c e

end CFSG.Quasithin.Chapter15.Section03.RankTwo.OriginalSource
