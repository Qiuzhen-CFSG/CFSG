module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.CoverRank.Calculation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.CoverRank.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# The complementary three-rank bound in B.5.11

Each of the five actual component-action cases supplies an injective S₃
homomorphism into the first factor. Restricting the genuine SQTK cover to
S₃ times an elementary abelian three-subgroup of its centralizer then gives
rank at most one by A.1.31(1). The complement here is literally C_D(G₁),
and the comparison consumer discharges its previous rank premise.

The only earlier-source parameter in the rank theorem is the full universal
A.1.31(1) implication, produced by `qt-a-01-section-rank`; final source
classification assembly retains its discharge. No S₃ subgroup or rank bound
is assumed by the component consumer. The comparison additionally retains
its existing B.5.1/B.5.5 and smaller-group classification inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.31(1),
printed pp.27–28, and B.5.8/B.5.11, printed pp.106 and 109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open QuasisimpleSource PreliminaryActions.Preparation
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {K : GroupClass.{u}}

/-- The actual centralizer complement has three-rank at most one. -/
theorem Conclusion.second_rank_le_one (c : Conclusion ρ)
    (h131 : FactorExtraction.EarlierA131One.{u}) (hyp : FFHypothesis K ρ) :
    primeRank 3 (centralizer (c.first : Set D)) ≤ 1 := by
  obtain ⟨cover⟩ := hyp.quotient
  obtain ⟨f, hf⟩ := c.actionCase.exists_symmetricThree_embedding ρ
  exact FactorExtraction.second_primeRank_le_one_of_symmetricThree h131 cover
    c.productConfiguration.product f hf

/-- B.5.11's smaller-factor comparison with its rank premise supplied by
A.1.31(1) on the original SQTK cover. -/
theorem Conclusion.compare_second_of_cover (c : Conclusion ρ)
    (h131 : FactorExtraction.EarlierA131One.{u})
    (h5 : ComponentInput.{u,v} K)
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hr : primeRank 3 c.component = 1)
    (hnot : ¬ AdequateAlternative ρ)
    (ih : SmallerClassification.{u,v} K (Nat.card D)) :
    (IsQuasisimple (generalizedFitting (centralizer (c.first : Set D))) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
        (c.productConfiguration.fixed.toRepresentation.comp
          (centralizer (c.first : Set D)).subtype)
        (generalizedFitting (centralizer (c.first : Set D))))) ∨
      Nonempty (SymmetricThreeCase (c.productConfiguration.fixed.toRepresentation.comp
        (centralizer (c.first : Set D)).subtype)) :=
  c.compare_second ρ h5 h1 hyp hr hnot ih (c.second_rank_le_one ρ h131 hyp)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
