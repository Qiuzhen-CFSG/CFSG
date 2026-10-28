module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.InitialReduction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.HighRank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.CompleteSourceInputs

/-!
# The actual B.5 source reduction for rank-one G.6

Apply the complete adequate B.5 classification to the original normal closure
of the transvection, using its genuine FF action and pulled-back SQTK cover.
The S3 branch proves the full G.6 conclusion, the hyperplane row contradicts
displacement generation, and the outer A6–C3 row contradicts the original
rank-one offender calculation. Exactly the complete quasisimple B.5.1 action
list and the literal two-factor quotient-action list remain.

The only universal premises are the independent earlier A.2, A.3.6 and B.4
source implications for the full known-simple catalogue. They are supplied to
the already proved B.5 induction; no G.6 classification premise is assumed.
Source: Aschbacher–Smith, G.6.4, pp.345–346; B.5.6–7, pp.105–106.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

/-- The two unresolved action branches retain their full original source data. -/
theorem Hypotheses.rank_one_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Conclusion ρ a ∨
      (IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))) ∧
        Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
          (ρ.comp (normalClosure ({a} : Set G)).subtype)
          (generalizedFitting (normalClosure ({a} : Set G))))) ∨
      Nonempty (SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) := by
  let := h.finite_group
  have hc := h.normalClosure_adequate_of_B_5_6
    (adequateClassification_knownSimple_of_earlier_classification hA h36 h4) ht
  cases hc with
  | quasisimple hq c => exact Or.inr (Or.inl ⟨hq, ⟨c⟩⟩)
  | symmetricThree c => exact Or.inl (h.conclusion_of_symmetricThree_normalClosure c)
  | twoFactors c => exact Or.inr (Or.inr ⟨c⟩)
  | outerSixThree c =>
    exact (h.normalClosure_not_outerShape
      (ChapterB.QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
        hA h36 h4 nonbinaryG2RootPairInput)
      (coverInput_of_a36 h36)
      (ChapterB.PreparationSource.componentInput ChapterB.PreparationSource.componentNormalization
        hA h36 h4) hA h36 ht c).elim
  | hyperplane c => exact (h.normalClosure_not_hyperplane c).elim
end CFSG.Quasithin.ChapterG.Section06
