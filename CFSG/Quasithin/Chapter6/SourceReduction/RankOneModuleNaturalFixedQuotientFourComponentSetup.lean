module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneFullReduced
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldOmega
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleOffender
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterA.Section04.Intersection
import all CFSG.Quasithin.ChapterA.Section04.Intersection

/-!
# The actual C.2.7 configuration at an omega-centralizer overgroup

If the two-generalized-Fitting preimage of a maximal two-local M₁ containing
C_G(Ω₁Z(T)) lies in M, A.4.4 recovers its two-core in M ∩ M₁. Its full
normalizer is M₁, so restriction gives the literal radical and characteristic
normalizer hypotheses of C.2.7. The original outside group prevents L from
lying in the intersection.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, using A.4.4 and C.2.7.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterA.Section04 RankOneGeneric
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ : Subgroup G} {n s : ℕ} [NeZero s]
local instance componentFixedAlgebra : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance componentBinaryModule : Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space s) :=
  Module.compHom (OrthogonalFourMinus.FiniteModel.Space s) (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField s))

/-- An actual maximal overgroup of the Sylow omega-centralizer supplies the
C.2.7 input if its two-generalized-Fitting preimage is contained in M. -/
theorem full_reduced_hermitian_component_input
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hF : twoGeneralizedFittingPreimage M₁ ≤ M) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple M (M₁.pCoreIn 2) (M ⊓ M₁) L := by
  let R := M₁.pCoreIn 2
  have hR₁ : R ≤ M₁ := pCoreIn_le 2 M₁
  have hRM : R ≤ M := (twoCore_le_fittingPreimage M₁).trans hF
  have hRne : R ≠ ⊥ := maximal_core_ne_bot M₁ hM₁
  have hNR : normalizer (R : Set G) = M₁ := (maximal_core_normalizer M₁ hM₁).symm
  have hcore : (M ⊓ M₁).pCoreIn 2 = R := by
    rw [inf_comm]
    apply (lemma_A_4_4_1 M₁ M (twoGeneralizedFittingPreimage M₁)
      (twoCore_le_fittingPreimage M₁)
      (le_inf (map_subtype_le _) hF) ?_).symm
    rw [twoCoreQuotientImage_fittingPreimage]
    refine Or.inr ⟨le_rfl, ?_, ?_⟩
    · rw [subgroupOf_self]
      exact IsSubnormal.top
    · exact (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
  have hrad : IsPRadical 2 (R.subgroupOf M) := by
    refine ⟨?_, ?_⟩
    · intro he
      have hh := congrArg (map M.subtype) he
      rw [map_subgroupOf_eq_of_le hRM, Subgroup.map_bot] at hh
      exact hRne hh
    · apply map_injective M.subtype_injective
      change ((normalizer (R.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = _
      rw [map_pCoreIn_of_injective 2 _ _ M.subtype_injective,
        ←subgroupOf_normalizer_eq hRM, subgroupOf_map_subtype, hNR, inf_comm,
        hcore, map_subgroupOf_eq_of_le hRM]
  have hcontrol : (R.subgroupOf M).characteristicNormalizerClosure ≤
      (M ⊓ M₁).subgroupOf M := by
    have hh := characteristicNormalizerClosure_subgroupOf_le hRM
      (maximal_core_characteristicNormalizerClosure M₁ hM₁).le
    intro x hx
    exact ⟨x.property, hh hx⟩
  have hRnormal : (R.subgroupOf (M ⊓ M₁)).Normal :=
    normal_subgroupOf_of_le_normalizer (by rw [hNR]; exact inf_le_right)
  have hSyl : Chapter1.IsSylowIn 2 R
      ((normalClosure (R.subgroupOf (M ⊓ M₁) : Set (M ⊓ M₁ : Subgroup G))).map
        (M ⊓ M₁).subtype) := by
    let := hRnormal
    rw [normalClosure_eq_self, map_subgroupOf_eq_of_le (le_inf hRM hR₁)]
    exact Chapter1.isSylowIn_iff.mpr
      ⟨isPGroup_pCoreIn 2 M₁, le_rfl, fun _ _ h₁ h₂ => le_antisymm h₂ h₁⟩
  have hi := h.reduced_enlargement.rankOneInput hout
  have hTL : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hLM₁ : ¬ L ≤ M₁ := by
    intro hle
    have he : M₁ = M := (hi.unique_local_join M₁ hM₁ (sup_le hle hTL)).trans
      h.maximal_eq_normalizer_L.symm
    obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
    have hH' := hH
    rw [h.maximal_eq_normalizer_L] at hH'
    exact hH.1.2 (((hi.hstar_centralizes_omega_of_hermitian hH' s hs hm).trans
      hCM₁).trans_eq he)
  let := h.L_normal
  have hLp : IsPPerfect 2 (L.subgroupOf M) := h.local_mem.2.2.1.of_surjective
    (subgroupOfEquivOfLe h.L_le).symm.toMonoidHom (subgroupOfEquivOfLe h.L_le).symm.surjective
  let := hi.quotient_quasisimple
  let e := subgroupOfEquivOfLe h.L_le
  let : IsQuasisimple ((L.subgroupOf M) ⧸ pCore 2 (L.subgroupOf M)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  refine ⟨⟨h.simpleQTKE.twoLocal_sqtk h.maximal.1, hRM, inf_le_left,
    hrad, hcontrol, hSyl⟩, ⟨h.L_le, ?_⟩, hi.quotient_quasisimple,
    h.local_mem.2.2.2.1, fun hh => hLM₁ (hh.trans inf_le_right), ?_⟩
  · exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      h.L_normal.isSubnormal hLp
  · exact hRM.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
