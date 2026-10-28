module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.LinearFour
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.Tits

/-!
# The original even-characteristic branch of 15.3.43

The genuine reduced configuration excludes every component in the even
characteristic source list. The larger-field and binary linear reductions
leave three exceptional models. The actual normal four-group places the G₂
local intersection in a root parabolic; triality and Tits use their intrinsic
Sylow and residual geometry. None of these arguments assumes that the source
involution's centralizer lies in M: the original centralizer is M_c.

The final consumer constructs the reduced configuration from the literal
15.3.43(a)--(e) inputs and rules out its S₃ shadow in every even-characteristic
case. The preceding source inputs and the other component families remain
with the full 15.3.43 assembly.

Source: Aschbacher--Smith, 15.3.33 and 15.3.43, printed pp.1134, 1139--1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The original reduced configuration excludes the entire even-characteristic
source catalogue without an extra involution-centralizer hypothesis. -/
theorem not_model_of_original_configuration
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hm : Model L z n) : False := by
  obtain ⟨_, hs, _, hmodel⟩ := remaining_exceptional_models_of_original c hm
  cases hmodel with
  | g2Derived iso => exact OriginalSource.not_g2_derived c hs iso
  | triality iso => exact OriginalSource.Triality.not_triality_of_original_configuration c hs iso
  | tits iso => exact not_tits_of_original_configuration c iso

/-- Literal application to the original 15.3.43 reduction, with every even
component case discharged and no replacement for the source centralizer M_c. -/
theorem source_not_symmetricThreeShadow_of_even_model
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    {z : G} {n : ℕ} (hm : Model L z n) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact not_model_of_original_configuration
    (reducedConfiguration_of_source d hI h hshadow halt) hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
