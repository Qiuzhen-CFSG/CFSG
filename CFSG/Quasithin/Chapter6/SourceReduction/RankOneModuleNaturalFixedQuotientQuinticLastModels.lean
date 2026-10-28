module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticRemainingModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernaryExclusion

/-!
# The last two actual component carriers

The complete original catalogue and the proved odd ternary exclusion leave
only J₄ and Tits as models of the same original core-central quotient.
Both alternatives remain explicit mathematical duties.

Source: Aschbacher--Smith6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The only remaining actual carriers of the original outside component. -/
theorem original_hermitian_component_jankoFour_or_tits
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Nonempty (coreCentralQuotient K ≃* Janko4.Model) ∨
      Nonempty (coreCentralQuotient K ≃* Tits.ParrottGroup) := by
  rcases original_hermitian_component_remaining_models
    h hout hm hM₁ hCM₁ hK hnot hq with ⟨p,hp,ho,unitary,hc⟩ | he
  · exact (original_hermitian_component_not_odd_ternary
      h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc).elim
  · exact he

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
