module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.SourceInterface
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Input

/-!
# C.2.7 input before identifying the constrained quotient

The original radical controls give the pushing-up setup without a rank or
outer-automorphism assumption on the unidentified component quotient. The
normalization of `L` by `Q₁` is kept explicit: it is the C.2.4 obligation in
the source catalogue, and cannot be obtained by assuming the cubic-residual
conclusion for an as yet unidentified quotient.

The resulting C.2.7 application gives the genuine star-group catalogue and
central comparison kernel. This is a group catalogue, not the still needed
block/parabolic catalogue of original 15.1.20--22.

Source: Aschbacher--Smith 15.1.20, pp.1094--1096; C.2.4 and C.2.7,
pp.144--147.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The radical input uses actual normalization, without `Facts` for an
unidentified quotient. It applies to both exchanged plane sizes. -/
theorem ExchangedSource.constrained_input_of_normalizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
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

/-- Apply checked source extraction to the actual component and radical.
Only the normalization obligation remains explicit. -/
theorem ExchangedSource.constrained_star_catalogue_of_normalizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hnL : d.Q1 ≤ normalizer (d.L : Set G)) :
    StarModels.Model (starImage d.L d.Q1 d.L) ∧
      (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
      (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
        Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  have hi := s.constrained_input_of_normalizes hG h hfit hnL
  exact ⟨star_model_from_source hi, coreToStar_ker_central_from_source hi,
    coreQuotient_center_card_from_source hi⟩

/-- Centerlessness alone makes the literal core-to-star map an isomorphism.
Neither the three-rank nor an outer-automorphism conclusion is assumed. -/
@[expose] noncomputable def constrained_coreStarEquiv_of_center_eq_bot
    (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hz : center (d.L ⧸ pCore 2 d.L) = ⊥) :
    (d.L ⧸ pCore 2 d.L) ≃* starImage d.L d.Q1 d.L :=
  MulEquiv.ofBijective (coreToStar hi.normalizes)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique
      ((coreToStar_ker_central_from_source hi).trans hz.le)),
      coreToStar_surjective hi.normalizes⟩

@[simp] theorem constrained_coreStarEquiv_of_center_eq_bot_apply
    (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hz : center (d.L ⧸ pCore 2 d.L) = ⊥) (x : d.L ⧸ pCore 2 d.L) :
    d.constrained_coreStarEquiv_of_center_eq_bot hi hz x = coreToStar hi.normalizes x := rfl

/-- A recognized star model transfers to the requested quotient through the
actual comparison map, once its central kernel has been eliminated. -/
theorem constrained_linear_quotient_of_centerless_star
    (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hz : center (d.L ⧸ pCore 2 d.L) = ⊥)
    (hm : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (starImage d.L d.Q1 d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hm
  exact ⟨n, hn, ⟨(d.constrained_coreStarEquiv_of_center_eq_bot hi hz).trans e⟩⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
