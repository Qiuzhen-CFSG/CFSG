module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEvenExclusion
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.OddNormalizer

/-!
# Excluding the Janko one carrier of the original outside component

The certified local bounds for J₁ give normalization of the supplied Sylow
subgroup by every solvable overgroup. Transporting this intrinsic property
through the actual marking contradicts the original quintic component
nonnormalization. The original actor is allowed to induce outer automorphisms.

Source: Aschbacher--Smith 6.1.4, printed p.665, and A.3.15(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

private theorem jankoOne_control : SolvableSylowControl 2 Janko1.Model := by
  intro S A hA hSA
  let := hA
  exact (Janko1.LocalStructure.odd_solvable_overgroup_card_dvd_twenty_one
    S A ⊥ hSA bot_le (by simp)).1

/-- The actual central quotient of the selected outside component cannot
be J₁, with the original component and Sylow subgroup retained. -/
theorem original_hermitian_component_not_jankoOne
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ Nonempty (coreCentralQuotient K ≃* Janko1.Model) := by
  rintro ⟨e⟩
  exact original_hermitian_component_no_solvable_sylow_control h hout hm hM₁ hCM₁ hK hnot hq
    (SolvableSylowControl.of_equiv e jankoOne_control)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
