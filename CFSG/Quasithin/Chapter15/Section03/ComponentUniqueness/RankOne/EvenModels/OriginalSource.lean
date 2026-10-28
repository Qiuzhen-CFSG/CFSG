module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction

/-!
# The source-valid part of the characteristic-two component inspection

The original source involution has C_G(z) = M_c, whereas the retained
`SourceInvolution S M z` interface assumes C_G(z) ≤ M. The larger-field
recognition and residual inspection do not use that stronger assumption.
Their premise-free cores therefore construct the actual Borel and exclude
all field degrees above one directly from the reduced configuration.

The same reduction also excludes the binary A₆ and PSL₅(2) alternatives
without a source-involution centralizer bound. Thus the original source
leaves precisely PSL₄(2), G₂(2)′, triality at two and the Tits group in this
characteristic-two branch. Their old conditional exclusions are not used
here: their placement arguments still require correction at the original
M_c/M boundary. The final theorem applies this reduction to the literal
configuration constructed from the earlier source inputs of 15.3.43.

Source: Aschbacher--Smith, 15.3.33(2)--(3) and 15.3.43,
printed pp.1134 and 1139--1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- Larger-field recognition uses the actual local configuration and model;
no involution-centralizer containment in M is required. -/
theorem largerFieldBorel_of_original_model
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hn : 1 < n) (hm : Model L z n) :
    LargerFieldBorel S M L n := by
  obtain ⟨hmodel, hB⟩ := ParabolicInspection.residual_inspection_of_model c hn hm
    (ParabolicInspection.quotientParabolic_of_model c hn hm)
  exact ParabolicInspection.largerFieldBorel_of_quotient c hmodel hB

/-- The actual larger-field source branch, independent of either global
centralizer M or M_c. -/
theorem not_larger_field_of_original_model
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hn : 1 < n) (hm : Model L z n) : False :=
  centralizers_ne c (larger_field_borel_centralizers c hn
    (largerFieldBorel_of_original_model c hn hm))

/-- The original hypotheses leave exactly the binary branches whose
legacy placement used the stronger global centralizer bound. -/
theorem remaining_binary_models_of_original
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ} (hm : Model L z n) :
    n = 1 ∧ IsSimpleGroup L ∧ ActsInner L z ∧
      (ClassicalGroup.IsPSL L 4 2 ∨ BinaryInspection.ExceptionalModel L) := by
  have hn : n = 1 := by
    have hp := hm.positive
    by_contra hne
    exact not_larger_field_of_original_model c (by omega) hm
  subst n
  refine ⟨rfl, ?_⟩
  cases BinaryInspection.remaining_model c hm with
  | linear hs d hd iso hi =>
    rcases hd with rfl | rfl
    · exact ⟨hs, hi, Or.inl iso⟩
    · exact (BinaryInspection.LinearInspection.not_linear_five_of_recognition c hs iso
        CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher.FlagRecognition.five).elim
  | exceptional hs he hi => exact ⟨hs, hi, Or.inr he⟩
  | alternatingSix iso _ =>
    exact (c.not_alternating_four (BinaryInspection.SixInspection.actor_alternating_four c iso)).elim

/-- Apply the corrected characteristic-two reduction to the original
15.3.43(a)--(e) producer, using precisely its original groups and planes. -/
theorem source_remaining_binary_models
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    {z : G} {n : ℕ} (hm : Model L z n) :
    n = 1 ∧ IsSimpleGroup L ∧ ActsInner L z ∧
      (ClassicalGroup.IsPSL L 4 2 ∨ BinaryInspection.ExceptionalModel L) :=
  remaining_binary_models_of_original
    (reducedConfiguration_of_source d hI h hshadow halt) hm

/-- The actual 15.3.43 contradiction in every larger-field
characteristic-two case, without the legacy involution-centralizer premise. -/
theorem source_not_symmetricThreeShadow_of_larger_field
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    {z : G} {n : ℕ} (hn : 1 < n) (hm : Model L z n) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact not_larger_field_of_original_model
    (reducedConfiguration_of_source d hI h hshadow halt) hn hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
