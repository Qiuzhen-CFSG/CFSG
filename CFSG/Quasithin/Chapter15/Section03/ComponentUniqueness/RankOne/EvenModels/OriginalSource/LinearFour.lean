module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.OriginalSource

/-!
# The original 15.3.43 consumer of binary four-dimensional exclusion

Apply the corrected middle-node argument to the literal reduced configuration
constructed from the earlier source inputs. Together with the larger-field,
A₆ and PSL₅(2) exclusions, this leaves only the three exceptional binary models.
The earlier source construction and the exceptional exclusions remain separate.

Source: Aschbacher--Smith, 15.3.43, printed pp.1139--1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The genuine even-characteristic configuration leaves only the exceptional
binary models after the original PSL₄(2) branch is excluded. -/
theorem remaining_exceptional_models_of_original
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hm : Model L z n) :
    n = 1 ∧ IsSimpleGroup L ∧ ActsInner L z ∧ BinaryInspection.ExceptionalModel L := by
  obtain ⟨hn, hs, hi, hlinear | he⟩ := remaining_binary_models_of_original c hm
  · exact (BinaryInspection.LinearInspection.not_linear_four_of_original_configuration
      c hs hlinear).elim
  · exact ⟨hn, hs, hi, he⟩

/-- The actual 15.3.43 contradiction when its component is PSL₄(2). -/
theorem source_not_symmetricThreeShadow_of_linear_four
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 4 2) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact BinaryInspection.LinearInspection.not_linear_four_of_original_configuration
    (reducedConfiguration_of_source d hI h hshadow halt) hs iso

/-- The remaining even-characteristic alternatives on the literal original
source producer, without the legacy involution-centralizer assumption. -/
theorem source_remaining_exceptional_models
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    {z : G} {n : ℕ} (hm : Model L z n) :
    n = 1 ∧ IsSimpleGroup L ∧ ActsInner L z ∧ BinaryInspection.ExceptionalModel L :=
  remaining_exceptional_models_of_original
    (reducedConfiguration_of_source d hI h hshadow halt) hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
