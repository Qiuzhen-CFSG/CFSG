module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple

/-!
# The original marked component theorem in an outside subgroup

The selected ordering maximum and the original orthogonal residual dichotomy
identify the distinguished partner with the centralizer of the central
involutions. That central subgroup has order two, so its generator lies in
the actual plane stabilizer and has centralizer exactly Mc.

The complete source15.3.11 supplies the outside Sylow control, trivial odd
core and characteristic-two intersection. These instantiate15.3.33(2) and
the known-simple source1.1.5, producing all five ordinary-component clauses
with the actual ambient conjugation action. The two local groups M and Mc
retain their separate source roles throughout.
Source: Aschbacher--Smith15.3.4 and15.3.33(2)--(3), printed pp.1121,1134.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marked involution, including its full ambient centralizer. -/
theorem source_central_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ d.S ∧
      (∀ t ∈ (d.T : Subgroup G), t * z = z * t) ∧
      centralizer ({z} : Set G) = d.Mc := by
  have hZ := d.action.card_centralInvolutions d.T d.sylow_le
  obtain ⟨hne, _, hmax⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany hZ
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton d.Mc
  have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  obtain ⟨N, hN, horder⟩ :=
    InitialSource.UniformControl.source_exists_ordering_maximal_above hG d.T ⟨hMc.1, hTMc⟩
  rw [hmax N hN] at horder
  have hC : d.Mc = centralizer (d.Z : Set G) :=
    centralizer_eq_Mc_of_residual_dichotomy d.T d.M d.Mc d.sylow_le
      ⟨hMc.1, hTMc⟩ hne hMc.2 horder
      ((source_lemma_15_3_2_4 d.T d.action hM (le_inf d.sylow_le hTMc)
        inf_le_left).imp id And.right)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := d.Z) 2
    (by simpa only [hZ] using (dvd_refl 2))
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hgen : zpowers (z : G) = d.Z :=
    eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by rw [Nat.card_zpowers, hzG, hZ])
  refine ⟨z, hzG, ?_, ?_, ?_⟩
  · exact (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)
      ((le_conjugateSpanBy _ _) z.property)
  · intro t ht
    exact centralInvolutions_le_centralizer_sylow d.T z.property t ht
  · calc
      centralizer ({(z : G)} : Set G) = centralizer (zpowers (z : G) : Set G) := by
        rw [zpowers_eq_closure, centralizer_closure]
      _ = centralizer (d.Z : Set G) :=
        congrArg (fun H : Subgroup G => centralizer (H : Set G)) hgen
      _ = d.Mc := hC.symm

/-- Every original ordinary component satisfies all five clauses of15.3.33(3). -/
theorem ordinary_component_structure_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    {K : Subgroup I} (hK : IsComponent I K) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ d.S ∧
      centralizer ({z} : Set G) = d.Mc ∧ Conclusions K d.M z := by
  obtain ⟨z, hz, hzS, hzT, hCz⟩ := source_central_involution hG d hempty hM hu hmany
  have hMc : d.Mc ∈ maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) :=
    hu ▸ Set.mem_singleton d.Mc
  have hTMc : (d.T : Subgroup G) ≤ d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  have hHe : d.Mc ∈ Chapter1.HeOver G (d.T : Set G) :=
    ⟨Chapter1.mem_He_iff.mpr (hG.evenCharacteristic d.T d.Mc hMc.1 hTMc),
      Chapter1.mem_H_of_isTwoLocal hMc.1.1, hTMc⟩
  have hSyl : OutsideSylowControl d.Yplus d.S d.M := fun J hJ =>
    (OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany J hJ).sylow
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hMI : generalizedFitting (d.M.subgroupOf I) = pCore 2 (d.M.subgroupOf I) := by
    rw [← inf_subgroupOf_right d.M I]
    let e := subgroupOfEquivOfLe (H := d.M ⊓ I) (show d.M ⊓ I ≤ I from inf_le_right)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, h11.generalized_fitting]
  refine ⟨z, hz, hzS, hCz, ?_⟩
  exact ordinary_component_structure hG
    (fun _ _ _ _ _ h => h.intersection_characteristicTwo)
    (fun h H P M z hh D hD => Chapter1.lemma_1_1_5_three_knownSimple h H P M z hh D hD)
    d.T hI hSyl inf_le_left hHe hz hzS hzT hCz h11.odd_core hMI hK

end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
