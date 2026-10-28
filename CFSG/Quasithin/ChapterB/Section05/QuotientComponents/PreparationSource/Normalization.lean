module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource

/-!
# Supplying actual B.1.5(4) to B.5.5

The unconditional source normalization theorem instantiates the exact universal
input used in the quotient-component preparation. The B.5.5 conclusion now
retains only its independent A.2, A.3.6 and corrected B.4.2 source inputs.
-/

public section
namespace CFSG.Quasithin.ChapterB.PreparationSource
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions
universe u v

/-- The full original-group and original-module B.1.5(4) input. -/
theorem componentNormalization : ComponentNormalizationInput.{u,v} := by
  intro D _ _ V _ _ _ σ hf A hA L hL
  exact source_lemma_B_1_5_4 σ hf hA hL

/-- B.5.5 with the component-normalization premise proved from its source. -/
theorem componentInput_of_classification_sources {K : GroupClass.{u}}
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} K) :
    Preparation.ComponentInput.{u,v} K :=
  componentInput componentNormalization hA h36 h4
end CFSG.Quasithin.ChapterB.PreparationSource
