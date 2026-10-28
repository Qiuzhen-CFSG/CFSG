module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Reduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.EarlierSources
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.FixedQuotientSum
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.BinaryUpper
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.CoverRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.FirstFactor
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.AmbientSecond
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# Rank-one factor extraction and B.5.11–12

The recursive call is made on exactly G₂=C_G(G₁) acting on V₂=C_V(G₁).
Nontriviality, strict order descent and all FF hypotheses are furnished by the
proved component descent. The actual SQTK cover and an S₃ subgroup of G₁
give the complementary rank bound. The exhaustive rank-one row extraction,
including the binary natural upper extension, then supplies B.5.11(2) on
that same restricted action. Natural and doubled rows retain their actual
moved spaces, and the exceptional row retains every B.4.8(3) clause.

In the supplemented B.5.10 configuration, the complementary module lifts
through V₂ ↪ V. Both original factor actions then satisfy B.5.6(3) on their
images modulo C_V(G), giving its required direct decomposition and
contradicting the counterexample condition. Thus B.5.12 leaves precisely
the exceptional first-factor configuration.

Earlier B.5.1 and B.5.5 producers are `qt-b05-quasisimple` and
`qt-b05-quotient-components`. The universal B.4.8(3) and A.1.31(1) inputs are
specified in EarlierSources, with their existing producers identified there.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.106 and 109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
universe u v

/-- An established rank-one classification supplies the full factor module,
including the nonsupplemented binary upper extension of B.4.8(3). The latter
universal earlier implication is discharged by the source assembly owner. -/
theorem rankOneModuleExtraction {K : GroupClass.{u}} (h48 : EarlierB48Three.{u,v}) :
    RankOneModuleExtraction.{u,v} K := by
  intro D _ _ _ V _ _ ρ hyp hr h
  exact BinaryUpper.classified_factor_module h48 hyp hr h

end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction

namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource PreliminaryActions.Preparation
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The remaining alternatives concern the literal complementary action from
the actual smaller-order recursive call. The rank premise is the independent
SQTK-cover obligation, not a presumed quotient-monotonicity principle. -/
theorem Conclusion.factor_or_binary_second (c : Conclusion ρ)
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G))
    (hsecond : primeRank 3 (centralizer (c.first : Set G)) ≤ 1) :
    let σ := c.productConfiguration.fixed.toRepresentation.comp
      (centralizer (c.first : Set G)).subtype
    Nonempty (FactorModuleConclusion σ) ∨
      ∃ s : MovedSection σ ⊤,
        IsLinearNatural (s.space.toRepresentation.comp
          (⊤ : Subgroup (centralizer (c.first : Set G))).subtype) BinaryField.two 3 ∧
        s.space.toSubmodule ⊔ Representation.invariants σ ≠ ⊤ := by
  obtain ⟨hn, _, hh⟩ := c.nontrivial_descent ρ h5 h1 hyp hr hnot
  let := hn
  exact FactorExtraction.classified_factor_or_binary hh hsecond
    (Or.inr (c.classify_second ρ h5 h1 hyp hr hnot ih))

/-- B.5.11(2) on precisely G₂=C_G(G₁) and V₂=C_V(G₁). The cover rank
calculation and the strictly smaller recursive call discharge the extraction
premises; the output retains the literal fixed quotient and all source rows. -/
theorem Conclusion.factor_module_second (c : Conclusion ρ)
    (h48 : FactorExtraction.EarlierB48Three.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    Nonempty (FactorModuleConclusion (c.productConfiguration.fixed.toRepresentation.comp
      (centralizer (c.first : Set G)).subtype)) := by
  obtain ⟨hn, _, hh⟩ := c.nontrivial_descent ρ h5 h1 hyp hr hnot
  let := hn
  exact FactorExtraction.BinaryUpper.classified_factor_module h48 hh
    (c.second_rank_le_one ρ h131 hyp)
    (Or.inr (c.classify_second ρ h5 h1 hyp hr hnot ih))

/-- B.5.12: the selected first factor is exceptional. In the supplement
branch both factor cases are constructed on actual ambient submodules; their
images form the source direct sum modulo the global fixed space. -/
theorem Conclusion.exceptional (c : Conclusion ρ)
    (h48 : FactorExtraction.EarlierB48Three.{u,v})
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card G)) :
    IsExceptional ρ c.first c.sectionData.space := by
  let := hyp.finite_module
  let : c.component.Normal := c.component_normal
  rcases c.productConfiguration.configuration with hs | he
  · obtain ⟨f⟩ := c.factor_module_second ρ h48 h131 h5 h1 hyp hr hnot ih
    exact c.exceptional_of_factor_cases ρ hnot
      (FactorExtraction.ambientSpace c f.space)
      (FactorExtraction.ambientSpace_supplement c f)
      (FactorExtraction.first_factor_case c.sectionData c.actionCase c.productConfiguration)
      (FactorExtraction.ambient_factor_case h48 c hs f)
  · exact he

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
