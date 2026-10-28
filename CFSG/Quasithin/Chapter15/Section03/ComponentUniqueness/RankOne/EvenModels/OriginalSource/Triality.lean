module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource.Triality.Placement

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource
public import Theory.SpecificGroups.Triality.BinaryCentralResidual

/-!
# Excluding the original binary triality component

The actual local subgroup and Sylow are simultaneously marked in one full
triality parabolic. Its arms Levi contradicts the source three-part bound.
For the central node, the proved highest-root calculation gives a trivial
Sylow centralizer of the literal three-residual. Transport to the original
action quotient contradicts the source's nontrivial V₁ action on L.

The parabolic is constructed from the original normal four-group and
minimality. No containment of the source involution centralizer in M occurs.

Source: Aschbacher--Smith, 15.3.43, printed pp.1139--1140.
-/

public section

open Subgroup
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource.Triality
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

include c in
private theorem false_of_central_residual_centralizer
    (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L)
    (hcentral : unipotent (binaryParameters 1 Nat.zero_lt_one) ⊓
      centralizer (threeResidualIn (parabolic (binaryParameters 1 Nat.zero_lt_one) .central) :
        Set (BinaryCarrier 1 Nat.zero_lt_one)) = ⊥) : False := by
  let d := c.toComponentAction
  obtain ⟨e, a, hM, hS⟩ := exists_marked_quotient_parabolic c hs iso
  cases a with
  | arms => exact not_arms_parabolic c hs e hM
  | central =>
    have hY : (d.image Yplus).map e.toMonoidHom =
        threeResidualIn (parabolic (binaryParameters 1 Nat.zero_lt_one) .central) := by
      rw [c.quotient.residual, threeResidualIn_map, hM]
    apply SporadicModels.reduced_image_centralizer_ne_bot c
    apply bot_unique
    rintro x ⟨hxS, hxY⟩
    have hx : e x ∈ unipotent (binaryParameters 1 Nat.zero_lt_one) ⊓
        centralizer (threeResidualIn (parabolic (binaryParameters 1 Nat.zero_lt_one) .central) :
          Set (BinaryCarrier 1 Nat.zero_lt_one)) := by
      refine ⟨hS ▸ mem_map_of_mem e.toMonoidHom hxS, ?_⟩
      intro y hy
      rw [← hY] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact (e.map_mul z x).symm.trans ((congrArg e (hxY z hz)).trans (e.map_mul x z))
    exact e.injective ((hcentral.le hx).trans (map_one e).symm)

include c in
/-- The triality alternative contradicts the literal original reduced configuration. -/
theorem not_triality_of_original_configuration
    (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) : False := by
  apply false_of_central_residual_centralizer c hs iso
  exact BinaryCentralResidual.unipotent_inf_centralizer_threeResidual_eq_bot
    (binaryParameters 1 Nat.zero_lt_one) rfl

/-- The actual 15.3.43 source consumer of the binary triality exclusion. -/
theorem source_not_symmetricThreeShadow_of_triality
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact not_triality_of_original_configuration
    (reducedConfiguration_of_source d hI h hshadow halt) hs iso

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource.Triality
