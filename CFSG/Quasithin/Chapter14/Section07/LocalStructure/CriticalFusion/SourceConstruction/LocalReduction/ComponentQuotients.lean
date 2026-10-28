module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableLocalExclusion

/-!
# Quasisimple component quotients in the original local family

The Fitting subgroup of the image of a C-component embeds in the ambient
Fitting subgroup by subnormality. Source 14.7.6 makes it a three-group.
The genuine A.3.6 classification then excludes the two nonquasisimple
alternatives. Transport through the component's exact two-core quotient
proves quasisimplicity of K/O₂(K), without an odd-core assumption.

Nonsolvability from 14.7.29 supplies an actual component in every original
local, and the proved 14.5.19 argument makes that component escape N_G(L).
The subsequent component-orbit module reduction uses these conclusions.

Source: Aschbacher–Smith, 14.7.6, 14.7.29–30, printed pp.1044,1055;
A.3.6, printed pp.43–45, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal image of every local C-component is an ordinary component
in the local two-core quotient. Source 14.7.6 already excludes both
nonquasisimple A.3.6 alternatives. -/
theorem local_component_star_isComponent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    IsComponent (HStar I) (K.map (QuotientGroup.mk' (pCore 2 I))) := by
  let B := K.map (QuotientGroup.mk' (pCore 2 I))
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  have hB : B.IsCComponent := hK.map_quotient (pCore 2 I)
  have hfit : IsPGroup 3 (fittingSubgroup B) := by
    have hp := (local_fitting_isThreeGroup h hab structural previous faithful I hI).to_le
      (fittingSubgroup_map_subtype_le_of_isSubnormal B hB.subnormal)
    exact hp.of_equiv (equivMapOfInjective (fittingSubgroup B) B.subtype B.subtype_injective).symm
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (HStar I) (local_star_sqtk h I hI) (pCore_quotient_pCore_eq_bot 2) B hB
  exact ⟨hB.subnormal,hc.isQuasisimple_of_fitting_isThreeGroup hB hfit⟩

/-- The quasisimplicity clause of source 14.7.30, for the intrinsic
K/O₂(K), transported through the exact component quotient map. -/
theorem local_component_twoCore_isQuasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := (local_component_star_isComponent h hab structural previous faithful I hI K hK).2
  exact IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm

/-- Every original local has a genuine C-component with its actual
quasisimple two-core quotient. The component escapes the original normalizer. -/
theorem local_exists_quasisimple_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ K : Subgroup I, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map I.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable
    (local_not_solvable d h hab structural previous faithful earlier I hI)
  exact ⟨K,hK,local_component_twoCore_isQuasisimple h hab structural previous faithful I hI K hK,
    local_component_not_le_normalizer h structural I hI K hK⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
