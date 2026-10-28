module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.FiveLarge
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.Four
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.FourActors.Source

/-!
# Zeroth closure from the original centralizer controls

In degree five, the proved mutually normalizing action theorem discharges
both rank exclusions in 12.1.3. The source model is constructed, and the
only earlier premise is nonsingular centralizer control. In degree four,
the proved mutual branch and finite H.9.3 actor obstruction discharge the
12.1.7 action premises after pure-intersection control is available.

The source order is preserved: degree-five closure does not use pure
fusion or degree-four closure. Nonsingular and pure centralizer controls
are still explicit source obligations. Their final discharge remains with
`qt-d-double-natural-centralizers` and `qt-d-1222-double-natural`.
Source: Aschbacher--Smith, 12.1.3 and 12.1.7, printed pp.789--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- The degree-five zeroth-closure conclusion, with both action exclusions
and the compatible source model supplied. Nonsingular centralizer control
is the remaining earlier source premise. -/
theorem doubledFive_zeroClosure_of_nonsingular_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hc
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
  exact D.doubledFive_zeroClosure_of_pair_of_many h hmany B
    (fun g hg hn => ZeroClosure.Mutual.five_mutual_centralizes M.setup M.representation_eq
      g (hg.trans (D.doubledOrbit_E322 h).normalizes) hn) S hc
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- Both degree-four action arguments are supplied on the literal chosen
orbit. Only the earlier nonsingular and pure centralizer conclusions remain. -/
theorem doubledFour_zeroClosure_of_controls_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → B.PureIntersectionCentralizes →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hc hp
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  exact D.doubledFour_zeroClosure_of_pair_of_many h hmany B
    (D.doubledFour_mutual_centralizes_of_many h hmany B S hp) S hc hp

/-- The full degree-four/five zeroth-closure conclusion from the two original
centralizer controls, with every action and model premise discharged. -/
theorem doubled_zeroClosure_of_controls_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → B.PureIntersectionCentralizes →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hc hp
  rcases B.degree with hn | hn
  · subst n
    exact D.doubledFour_zeroClosure_of_controls_of_many h hmany B hc hp
  · subst n
    exact D.doubledFive_zeroClosure_of_nonsingular_of_many h hmany B hc
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
