module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Preparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Groups
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Quasisimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products

/-!
# Extracting the two L₃(2) module cases in 13.6.20

The adequate B.5.6 implication applies to the literal best-offender subgroup
of the faithful action on W_K. Its hypotheses use the original group class,
the actual SQTK cover, and the actual component image. A classified module
on that subgroup returns to the original action, with its moved space and
central denominator unchanged.

The actual component isomorphism excludes the incompatible group alternatives.
The exhaustive quasisimple comparison and the product/hyperplane module proofs
then give the natural component-fixed quotient, with commutator generation,
or the doubled moved space itself. The product splitting uses the full earlier
B.5.1 implication; its universal row-extraction premise is discharged here.

Only the full corrected B.5.1 and adequate B.5.6 implications remain explicit,
along with the independent `ClassifierApplicability` input. The concrete W_K
specialization retains the literal plus image of K. Final source assembly,
including the applicability producer, remains with the 13.6.20 consumer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1 and B.5.6,
printed pp.99–105, and 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
open ComponentSelection ChapterB.QuasisimpleSource
universe u w

/-- Return the classified offender restriction with no change of module. -/
theorem moduleCase_of_offender {D : Type u} [Group D] [Finite D]
    {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : ClassifierApplicability 𝒦 ρ C)
    (hcase : LinearThreeModuleCase (ρ.comp (offenderSubgroup ρ).subtype)
      (C.subgroupOf (offenderSubgroup ρ))) : LinearThreeModuleCase ρ C := by
  let : C.Normal := h.normal
  exact lift_case h.le_offenders hcase

/-- Only the three genuine module branches remain on the literal offender actor. -/
theorem offender_source_cases {D : Type u} [Group D] [Finite D]
    {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : ClassifierApplicability 𝒦 ρ C) (e : C ≃* Matrix.PSL3Two.PSL)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,w} 𝒦) :
    let σ := ρ.comp (offenderSubgroup ρ).subtype
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      σ (C.subgroupOf (offenderSubgroup ρ))) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  let : (C.subgroupOf (offenderSubgroup ρ)).Normal := offender_component_normal h
  exact source_cases (offender_component_equiv h e) (offender_alternative h e classification)

/-- The full corrected universal classifiers give the two component module
cases. Applicability is established on the actual offender subgroup, all
remaining source branches are exhausted, and the resulting literal moved
section is transported back to the original action. -/
theorem moduleCase_of_classifications {D : Type u} [Group D] [Finite D]
    {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
    (h : ClassifierApplicability 𝒦 ρ C) (e : C ≃* Matrix.PSL3Two.PSL)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,w} 𝒦)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,w} 𝒦) :
    LinearThreeModuleCase ρ C := by
  have rows : Products.QuasisimpleRowExtraction.{u,w} := by
    intro E _ _ W _ _ _ σ L _ eL c
    exact quasisimple_case eL c
  apply moduleCase_of_offender h
  let : (C.subgroupOf (offenderSubgroup ρ)).Normal := offender_component_normal h
  rcases offender_source_cases h e classification with hq | hp | hh
  · exact hq.elim (quasisimple_case (offender_component_equiv h e))
  · exact hp.elim (Products.twoFactor_moduleCase earlier rows (offender_hypothesis h)
      (offender_component_equiv h e))
  · exact hh.elim (Products.hyperplane_moduleCase (offender_hypothesis h)
      (offender_component_equiv h e))

variable {G : Type u} [Group G] [Finite G]
  {𝒦 : GroupClass.{u}} (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  [IsElementaryAbelian 2 (WK K L T z v)]

/-- The full adequate alternatives on the actual offender subgroup of W_K. -/
theorem wk_offender_alternative
    (h : ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦) :
    let σ := wkRepresentation K L T z v hL hz
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      (σ.comp (offenderSubgroup σ).subtype) :=
  offender_alternative h e classification

/-- The three remaining source branches on W_K, with the literal component image. -/
theorem wk_offender_source_cases
    (h : ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦) :
    let σ := wkRepresentation K L T z v hL hz
    let τ := σ.comp (offenderSubgroup σ).subtype
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion τ
      ((plusImage K L T z v hL hz K).subgroupOf (offenderSubgroup σ))) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase τ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase τ) :=
  offender_source_cases h e classification

/-- Return a classified restricted module to the literal plus action on W_K. -/
theorem wk_moduleCase_of_offender
    (h : ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (hcase : let σ := wkRepresentation K L T z v hL hz
      LinearThreeModuleCase (σ.comp (offenderSubgroup σ).subtype)
        ((plusImage K L T z v hL hz K).subgroupOf (offenderSubgroup σ))) :
    LinearThreeModuleCase (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K) :=
  moduleCase_of_offender h hcase

/-- Apply the universal classifiers to the actual plus action on W_K and
the literal image of K. The independent applicability producer supplies `h`;
the existing `doubled_of_moduleCase` consumer can use this result directly. -/
theorem wk_moduleCase_of_classifications
    (h : ClassifierApplicability 𝒦 (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (e : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u} 𝒦)
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦) :
    LinearThreeModuleCase (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K) :=
  moduleCase_of_classifications h e earlier classification

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
