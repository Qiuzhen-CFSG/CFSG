module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoActionSource
public import Theory.SpecificGroups.Janko4.Model.SevenNonreal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcluded

/-!
# The J4 exclusion and the original doubled-natural centralizers

The full binary point automizer contains a real seven-element. Coprime lifting
preserves reality in the literal J4 image, contradicting the native nonreality
theorem. That theorem follows from the two full involution centralizers and
the small Golay-cocode trace certificate, with no ambient seven-centralizer
upper bound. Thus source 12.1.1--3 and all three degree-five conclusions are
proved with their original hypotheses, full covering centers and quotient maps.
Degree five uses only the relative placement proved in the source.

The two-degree endpoint retains exactly the independently owned degree-four
MarkedOmegaFixed premise, with qt-d-double-natural-pure-fusion and
qt-rank-two-ms93. This is not an unconditional proof of degree-four 12.1.4--7.
Source: Aschbacher--Smith, printed pp.788--792/PDF pp.805--809.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

/-- Neither degree admits the literal J4 point-join configuration. -/
theorem no_jankoFour_pointJoin_model
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ JankoPointJoinModel n := by
  rintro ⟨H,E,_,_,_,_,_,_,⟨e⟩,_⟩
  exact Janko4.SevenNonreal.no_binary_automizer_section
    (n-1) (by rcases hn with rfl | rfl <;> simp) H e

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Nonsingular centralizers in both degrees, the rank bound, and degree-five
positive zeroth closure, from the original source hypotheses. -/
theorem doubleNatural_nonsingular_controls_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  exact D.doubleNatural_nonsingular_controls_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model B.degree)

/-- All three original degree-five conclusions, using the completed pure-point family. -/
theorem doubleNatural_five_conclusions_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_five_conclusions_of_no_jankoFour_pointJoin_model_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model (Or.inr rfl))

/-- The only remaining premise for the two-degree assembly is the
independently owned degree-four marked MS conclusion. -/
theorem doubleNatural_conclusions_of_omega_fixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  exact D.doubleNatural_conclusions_of_no_jankoFour_pointJoin_model_of_omega_fixed_of_many
    h hmany B (Nonsingular.no_jankoFour_pointJoin_model B.degree)

/-- The actual terminal reduction now receives nonsingular control without
an extra source premise. The later weak-closure, odd-fixed-space and generation
inputs remain with the final doubled-natural branch owner. -/
theorem doubleNatural_excluded_of_many_of_remaining_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (2 : ℕ∞) < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T)
    (hgen : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      ChapterE.generationParameter H = 2) :
    letI := D.doubledOrbit_elementary h
    B.OddFixedSpaces → False := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  exact D.doubleNatural_excluded_of_many_of_geometry h hmany B hw hgen
    (D.doubleNatural_nonsingular_controls_of_many h hmany B).1 hfixed

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
