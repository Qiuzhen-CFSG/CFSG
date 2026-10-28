module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# The constrained component before the source row exclusions

The radical and characteristic-normalizer controls of 15.1.18 give the
literal C.2.7 input for the chosen component as soon as Q₁ normalizes it.
Restriction to LQ₁, where L is relatively normal, puts O₂(LQ₁) in Q₁.
Self-centralization of that core then embeds Ω₁Z(Q₁) in the actual star
module. Neither normality in G₁ nor a model for L/O₂(L) is assumed.

The final extraction retains the full star-group catalogue and the central
kernel of the actual core-to-star map. It does not assert the seven rows of
15.1.22: Q₁-normalization, block reconstruction, parabolic placement, and
the preceding rank-one exclusions remain source obligations.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095, and C.2.7,
printed pp.145--147. These results apply before 15.1.23--24.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Construct C.2.7 from the original pre-exclusion data. The explicit
normalizer premise is the earlier C.2.4 obligation, not a consequence of
characteristic two for G₁, which is not among the hypotheses. -/
theorem PreExclusionSource.constrained_input_of_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hnL : d.Q1 ≤ normalizer (d.L : Set G)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L := by
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
    d.L_component, s.quasisimple, hfit, d.L_not_le_MZ, hnL⟩

/-- Relative normality in LQ₁ suffices for the core containment and the
omega-center embedding. No cubic-residual identification of L is needed. -/
theorem preExclusion_radical_omega (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L) :
    (d.L ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 ∧
      omegaOneCenterAmbient d.Q1 ≤
        (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype := by
  let : (d.L.subgroupOf (d.L ⊔ d.Q1)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  have hQR := source_joinCore_le_radical (source_join_input hi)
  have hc : centralizer (pCore 2 d.L : Set d.L) ≤ pCore 2 d.L := by
    rw [← hi.fitting]
    exact centralizer_generalizedFitting_le d.L
  have hJc := centralizer_pCore_sup_le 2 d.L d.Q1 hc
    (isPGroup_pCoreIn 2 d.MZ) hi.normalizes
  refine ⟨hQR, ?_⟩
  intro x hx
  obtain ⟨hxR, hx2, hcent⟩ := (mem_omegaOneCenterAmbient_iff d.Q1 x).mp hx
  let J := d.L ⊔ d.Q1
  let xJ : J := ⟨x, mem_sup_right hxR⟩
  have hxC : xJ ∈ centralizer (pCore 2 J : Set J) := by
    intro a ha
    exact Subtype.ext (hcent a (hQR (mem_map_of_mem J.subtype ha)))
  refine ⟨xJ, ?_, rfl⟩
  change xJ ∈ omegaOneCenterAmbient (pCore 2 J)
  exact (mem_omegaOneCenterAmbient_iff _ xJ).mpr
    ⟨hJc hxC, Subtype.ext hx2, fun a ha => hxC a ha⟩

/-- The genuine C.2.7 group catalogue on the literal star image, retaining
the central cover comparison instead of identifying two different quotients. -/
theorem PreExclusionSource.constrained_star_catalogue_of_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hnL : d.Q1 ≤ normalizer (d.L : Set G)) :
    StarModels.Model (starImage d.L d.Q1 d.L) ∧
      (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
      (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
        Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  have hi := s.constrained_input_of_normalizes (h := h) hG hfit hnL
  exact ⟨star_model_from_source hi, coreToStar_ker_central_from_source hi,
    coreQuotient_center_card_from_source hi⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
