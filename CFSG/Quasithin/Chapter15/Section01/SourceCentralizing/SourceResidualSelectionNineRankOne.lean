module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSolvableControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.OrbitBorel

/-!
# The constrained rank-one-or-star alternative from local residual control

The actual orbit Borel is invariant under M_Z and has characteristic two
and odd quotient. Its control needs only the normalizer bound for O²(M_Z).
This proves the full natural rank-one alternative on the selected component.
The alternating-five branch and the remaining literal star comparison use
the existing original-component arguments without global residual input.

The Nine applications derive that local bound from the actual overgroup
pair and retain the same component, Sylow subgroup and star map. The star
alternative remains explicit; no complete component catalogue is asserted.

Source: Aschbacher--Smith 15.1.19(2), 15.1.20(2a), printed pp.1093--1094;
C.1.9 and C.2.7, printed pp.123 and 145--146.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem linearTwo_borel_of_local_residual
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hlocal : d.L ∈ Chapter1.L G d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) :
    d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,hlocal⟩
  have hs := d.localFamily_orbitBorel_structure hk hq hb.2.1
  have hn := d.localFamily_linearTwo_orbit_normalized_of_cComponent hG h hu hSyl
    hk d.L_component.2 d.L_not_le_MZ hb
  have hB := d.constrained_solvable_control_of_local_residual hG hu h hSyl hcontrol hbound
    (d.orbitSylowBorel_local hk.1).1 hn hs.1 hs.2.2
  apply le_antisymm (d.localFamily_linearTwo_borel_bound hu hk d.L_not_le_MZ hb)
  rw [←d.localSylowBorel_eq]
  exact le_inf ((le_conjugateSpanBy _ _).trans hB) inf_le_left

/-- The original component has the complete constrained rank-one-or-star
alternative from its literal marked residual-normalizer bound. -/
theorem PreExclusionSource.constrained_rankOne_or_star_of_local_residual
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne (h := h) hG hfit with hb | hs
  · rcases hb with ⟨n,hb⟩ | hb
    · have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
      exact Or.inl ⟨Or.inl ⟨n,hb⟩,
        linearTwo_borel_of_local_residual d hG hu h s.local_component s.quasisimple
          s.centralizer_sylow s.characteristic_control hbound hb,
        (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
          d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩
    · exact Or.inl (s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu hb)
  · exact Or.inr hs

/-- Both exchanged-plane sizes have the same complete constrained alternative
using the exact local residual bound. -/
theorem ExchangedSource.constrained_rankOne_or_star_of_local_residual
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne hG h hfit with hb | hs
  · rcases hb with ⟨n,hb⟩ | hb
    · have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
      exact Or.inl ⟨Or.inl ⟨n,hb⟩,
        linearTwo_borel_of_local_residual d hG hu h s.local_component s.quasisimple
          s.centralizer_sylow s.characteristic_control hbound hb,
        (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
          d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩
    · exact Or.inl (s.constrained_rankOne_of_alternatingFive hG hempty hM hJ hu h hb)
  · exact Or.inr hs

/-- The actual Nine overgroup pair discharges the local residual bound for
the complete constrained rank-one-or-star alternative. -/
theorem PreExclusionSource.nine_constrained_rankOne_or_star
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hbound := h.marked_residual_normalizer_control_of_pair hG T hempty hM hmany hJ hu
    hpair d.Z1_le_fixed d.Z1_ne_bot s.sylow_normalizes_MZ s.centralizer_sylow
  exact s.constrained_rankOne_or_star_of_local_residual (h := h) hG hempty hM hJ hu hbound hfit

/-- The actual Nine overgroup pair discharges the local residual bound for
the complete constrained rank-one-or-star alternative. -/
theorem ExchangedSource.nine_constrained_rankOne_or_star
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hbound := h.marked_residual_normalizer_control_of_pair hG T hempty hM hmany hJ hu
    hpair d.Z1_le_fixed d.Z1_ne_bot s.sylow_normalizes_MZ s.centralizer_sylow
  exact s.constrained_rankOne_or_star_of_local_residual h hG hempty hM hJ hu hbound hfit

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
