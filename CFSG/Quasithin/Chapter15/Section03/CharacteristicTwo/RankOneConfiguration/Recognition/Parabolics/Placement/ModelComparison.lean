module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Shadow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.SourceTransport

/-!
# Intrinsic consequences of the linear model comparison

The two regular models retain actual multiplicative equivalences and binary
field parameters. Their centers are trivial and their actual outer groups
are abelian, so the S₃ shadow gives the literal inner action of Y₊* on L*.
The even-degree SL₃ alternative has center of order three. These conclusions
have exactly the form consumed by Placement's containment argument.

The complete A.3.18/B.5.6 comparison is not yet proved here. In particular,
`comparison_of_reduced_models` still takes its reduced model alternatives
as an intermediate premise. Extracting the full component catalogue from
the genuine Thompson action and comparing its rank-two cases with A.3.18
remain obligations of this module's final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(2), printed p.1131 (PDF p.1148), and B.5.6, printed p.105.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- The source's middle alternative, with every inner-action premise discharged
from the actual models and the genuine shadow. -/
theorem centerless_inner_action_of_regular_model
    {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hn : (c.L.subgroupOf I).Normal)
    (hm : RegularModel (d.starImage I c.L)) :
    center (d.starImage I c.L) = ⊥ ∧
      ∀ y : d.starImage I d.Yplus, ∃ l : d.starImage I c.L,
        ∀ x : d.starImage I c.L,
          (l : d.Star I) * x * l⁻¹ = y * x * y⁻¹ :=
  ⟨hm.center_and_outer.1, inner_action_of_shadow d hI c h hn hm.center_and_outer.2⟩

/-- The exceptional linear model has intrinsic center of order three. -/
theorem center_card_three_of_even_linearThree {H : Type*} [Group H]
    (F : BinaryField) (hn : Even F.degree) (e : H ≃* SL(3, F.Carrier)) :
    Nat.card (center H) = 3 := by
  have hm : Nat.card F.Carrier % 3 = 1 := by
    rw [F.card_eq, Nat.BinaryTorusParity.two_pow_mod_three, Nat.even_iff.mp hn]
    rfl
  have hc := Matrix.SL3.card_center_eq_three_of_ne_bot F.Carrier
    (fun he => ((Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mp he) hm)
  exact (Nat.card_congr (centerCongr e).toEquiv).trans hc

/-- Convert genuine reduced model alternatives to the exact intrinsic
placement output. Producing the model alternatives remains a separate step;
this is not asserted to be the full A.3.18/B.5.6 comparison. -/
theorem comparison_of_reduced_models
    {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hn : (c.L.subgroupOf I).Normal)
    (hm : c.L = theta I ∨ RegularModel (d.starImage I c.L) ∨
      ∃ F : BinaryField, Even F.degree ∧ Nonempty (d.starImage I c.L ≃* SL(3, F.Carrier))) :
    c.L = theta I ∨
      (center (d.starImage I c.L) = ⊥ ∧
        ∀ y : d.starImage I d.Yplus, ∃ l : d.starImage I c.L,
          ∀ x : d.starImage I c.L,
            (l : d.Star I) * x * l⁻¹ = y * x * y⁻¹) ∨
      Nat.card (center (d.starImage I c.L)) = 3 := by
  rcases hm with ht | hr | ⟨F, he, ⟨e⟩⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl (centerless_inner_action_of_regular_model d hI c h hn hr))
  · exact Or.inr (Or.inr (center_card_three_of_even_linearThree F he e))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
