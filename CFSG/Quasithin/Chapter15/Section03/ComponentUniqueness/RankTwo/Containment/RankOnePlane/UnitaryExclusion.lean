module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.LocalCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.OrthogonalCore
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Excluding PSU₃(4) in the oriented component-plane configuration

The actual unitary model supplies the rank-one Borel facts, an element of
order five in that Borel, and control of the Sylow center by normalizer
two-cores. The five-element centralizes V and hence lies in M ∩ Mc ∩ I.
Consequently O₂(M ∩ Mc) ∩ I centralizes the chosen plane. The actual residual
construction makes O₂(M ∩ Mc) act nontrivially on V, whereas the orthogonal
Sylow calculation detects that action on the chosen plane already inside S.
Since S ≤ I, these two conclusions contradict each other.

All local constructions come from `CharacteristicTwo.LocalData`; in
particular Y is the actual residual and S the actual plane stabilizer.
Component normality is relative to I. The intrinsic unitary field order is
four, so its matrix field has order sixteen. The final exclusion has no
five-element, core-control, orthogonal-detection, or A₄ premise. The Borel
equality and identification of the oriented plane with the Sylow center
remain explicit inputs from the preceding Borel and `UnitaryField` results.
The ambient-center variant consumes the latter result's literal equality.
Exhaustion of `RankOneAlternative` and the rest of 15.3.40 remain with the
parent assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.2--12, 15.3.33--38, and the proof of 15.3.40,
printed pp.1121--1125 and 1134--1138.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion

variable {G : Type*} [Group G] [Finite G]

/-- The actual model, including its field and Hermitian involution, gives
the Borel facts without an additional characteristic-two premise. -/
theorem unitary_four_borel_facts {L S : Subgroup G}
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = S ⊓ L) :
    RankOneBorelFacts L S := by
  apply rankOneBorelFacts_of_sylow L S P hP
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  apply rankOneSylowFacts_of_equiv P e
  exact rankOneSylowFacts_psu3 J 2 (by decide) hcard hconj _

/-- The local reduction to a five-element, Sylow-center control, and
orthogonal detection. `exclusion_of_unitary_four` discharges all three
calculations from the actual model and natural action. -/
theorem exclusion_of_core_calculations
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i)
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = d.S ⊓ L)
    (hB : d.M ⊓ L = borel L d.S)
    (hfive : ∃ x : G, x ∈ borel L d.S ∧ orderOf x = 5)
    (hcontrol : FiveCoreControl L (d.S ⊓ L) (d.action.plane i))
    (hdetect : ∀ D : Subgroup G, D ≤ (d.T : Subgroup G) →
      (d.T : Subgroup G) ≤ normalizer (D : Set G) →
      ¬ D ≤ centralizer (d.V : Set G) →
      ¬ D ⊓ d.S ≤ centralizer (d.action.plane i : Set G)) : False := by
  obtain ⟨hDT, hTD⟩ := intersection_core_sylow_data d hMc
  apply hdetect _ hDT hTD (core_not_centralizing_of_plane_generation d L i hgen)
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  exact (inf_le_inf_left _ hSI).trans
    (local_core_centralizes_of_five_control d h hMc
      (unitary_four_borel_facts hm P hP) hB hfive hcontrol)

/-- The conditional PSU₃(4) exclusion in the oriented source configuration.
`hMc` is 15.3.4, `h` retains the preceding local component conclusions,
and `hgen` is the oriented plane generation in the proof of 15.3.40.
The parent supplies `hB` from the Borel argument and `hW` from the unitary
field calculation. All core-action calculations are discharged here. -/
theorem exclusion_of_unitary_four
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i)
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = d.S ⊓ L)
    (hB : d.M ⊓ L = borel L d.S)
    (hWL : d.action.plane i ≤ L)
    (hW : (d.action.plane i).subgroupOf L =
      (center (P : Subgroup L)).map (P : Subgroup L).subtype) : False := by
  obtain ⟨hfive, hcontrol⟩ := unitary_four_model_core hm P hP hWL hW
  exact exclusion_of_core_calculations d h hMc i hgen hm P hP hB
    hfive hcontrol (normal_sylow_core_detects_plane d i)

/-- The same exclusion using the exact ambient-center conclusion of
`unitary_plane_degree_eq_two`. Injectivity of L → G transports that
conclusion to the intrinsic center of the marked Sylow P. -/
theorem exclusion_of_unitary_four_of_ambient_center
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i)
    (hm : ClassicalGroup.IsPSU L 3 4) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = d.S ⊓ L)
    (hB : d.M ⊓ L = borel L d.S)
    (hWL : d.action.plane i ≤ L)
    (hW : d.action.plane i =
      (center (d.S ⊓ L : Subgroup G)).map (d.S ⊓ L).subtype) : False := by
  apply exclusion_of_unitary_four d h hMc i hgen hm P hP hB hWL
  apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
  rw [map_subgroupOf_eq_of_le hWL,
    map_subgroup_center_eq L.subtype L.subtype_injective, hP]
  exact hW

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
