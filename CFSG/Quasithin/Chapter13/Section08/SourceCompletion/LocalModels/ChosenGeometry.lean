module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Chosen
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EarlierGeometry

/-!
# Critical geometry for the unchanged standing local setup

The natural A₆ setup itself reconstructs the original Irr⁺ choice. Applying
the checked source geometry to that reconstruction preserves the original
L, V, Sylow flag and critical pair. Thus no ChosenModule or geometric
conclusion is added to the existing LocalSetup interface. The genuine
13.5.7 F.9 applicability hypothesis remains with its source producer;
13.7.8 is exactly the abelian span already present in LocalSetup.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The literal earlier-geometry input of the existing reorientation consumer. -/
theorem local_earlierGeometry (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V) :
    Reorientation.EarlierGeometry c V₃ V₁ :=
  (localNaturalSetup d).earlierGeometry d.abelian_span hF9 c

/-- The actual opposite critical-pair selection on the same original groups. -/
theorem local_exists_reversal_of_strict (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V)
    (hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃) :
    Nonempty (Reversal c) :=
  (localNaturalSetup d).exists_reversal_of_strict d.abelian_span hF9 c hstrict

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
end
