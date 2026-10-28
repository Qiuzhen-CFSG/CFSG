module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoActionSource
public import Theory.SpecificGroups.Janko4.Model.SevenCentralizerBounds

/-!
# Applying the weaker remaining J4 centralizer bound

The certified symmetric-linear quotient now proves that 840 divides the
centralizer order of every native seven-element. Sylow's normalizer
congruence excludes real sevens once the specified representative has
centralizer order less than 3360. The source applications below therefore
retain only this upper bound, rather than an exact centralizer count.

The upper bound remains with qt-d-double-natural-centralizers. It is not
asserted by these conditional applications. Degree four also retains the
original marked MS premise with qt-d-double-natural-pure-fusion and
qt-rank-two-ms93. Degree five requires no ambient Sylow containment.
All original quotient maps, covering centers and the source order of the
nonsingular, degree-five closure, pure-point and degree-four closure steps
are retained. Source: Aschbacher--Smith 12.1.1--7, printed pp.788--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

/-- The remaining strict ambient bound excludes the actual local configuration. -/
theorem no_jankoFour_pointJoin_model_of_seven_centralizer_lt
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) < 3360)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ JankoPointJoinModel n := by
  rintro ⟨H,E,_,_,_,_,_,_,⟨e⟩,_⟩
  exact Janko4.SevenCentralizerBounds.no_binary_automizer_section_of_representative_centralizer_lt
    hc (n-1) (by rcases hn with rfl | rfl <;> simp) H e

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonsingular and degree-five closure application, conditional
only on the strict centralizer bound in the actual J4 carrier. -/
theorem doubleNatural_nonsingular_controls_of_seven_centralizer_lt_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) < 3360) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  exact D.doubleNatural_nonsingular_controls_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_lt hc B.degree)

/-- All three degree-five source conclusions follow from the remaining
single native centralizer bound, using the completed pure-point family. -/
theorem doubleNatural_five_conclusions_of_seven_centralizer_lt_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) < 3360) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_five_conclusions_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_lt hc (Or.inr rfl))

/-- The two-degree assembly retains the concrete seven-centralizer bound and
the independently owned degree-four marked MS premise. -/
theorem doubleNatural_conclusions_of_seven_centralizer_lt_of_omega_fixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hc : Nat.card (centralizer
      (zpowers Janko4.SevenNormalizers.representative : Set Janko4.Model)) < 3360) :
    letI := D.doubledOrbit_elementary h
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_conclusions_of_no_jankoFour_pointJoin_model_of_omega_fixed_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model_of_seven_centralizer_lt hc B.degree)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
