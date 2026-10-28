module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoActionSource
public import Theory.SpecificGroups.Janko4.Model.SevenNormalizers

/-!
# Applying the remaining J4 seven-centralizer certificate

The full point automizer in the literal point-join image contains a real
seven-element in each degree. Its two-core kernel is coprime to seven, so
that element and its inverse are conjugate upstairs. The native J4
normalizer congruence excludes this once the centralizer of the specified
matrix word is proved to have order 840.

This is a conditional source reduction. The concrete centralizer count
remains with qt-d-double-natural-centralizers; no finite-model table entry
is used as a proof. The degree-four marked MS premise retains its existing
producers qt-d-double-natural-pure-fusion and qt-rank-two-ms93. The source
order, full covering center and original quotient maps are unchanged.
In particular the degree-five application requires no ambient Sylow
containment. Source: Aschbacher--Smith 12.1.1--7, printed pp.788--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

/-- The literal J4 certificate excludes the compressed configuration as
well as the stronger source action. Its proof remains an explicit premise. -/
theorem no_jankoFour_pointJoin_model_of_seven_centralizer_card
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) = 840)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ JankoPointJoinModel n := by
  rintro ⟨H,E,_,_,_,_,_,_,⟨e⟩,_⟩
  exact Janko4.SevenNormalizers.no_binary_automizer_section_of_representative_centralizer_card
    hc (n-1) (by rcases hn with rfl | rfl <;> simp) H e

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonsingular and degree-five closure application, conditional
only on the explicit centralizer count in the actual J4 carrier. -/
theorem doubleNatural_nonsingular_controls_of_seven_centralizer_card_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) = 840) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  exact D.doubleNatural_nonsingular_controls_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_card hc B.degree)

/-- All three degree-five source conclusions follow from the remaining
single native centralizer count, using the completed pure-point family. -/
theorem doubleNatural_five_conclusions_of_seven_centralizer_card_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) = 840) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_five_conclusions_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_card hc (Or.inr rfl))

/-- The two-degree assembly retains the concrete seven-centralizer count and
the independently owned degree-four marked MS premise. -/
theorem doubleNatural_conclusions_of_seven_centralizer_card_of_omega_fixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) = 840) :
    letI := D.doubledOrbit_elementary h
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_conclusions_of_no_jankoFour_pointJoin_model_of_omega_fixed_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_card hc B.degree)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
