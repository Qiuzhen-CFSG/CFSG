module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarFixed
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourMiddleStarSource
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Assembly

/-!
# Discharging the degree-four fixed-space premise of centralizer assembly

The natural-plus-dual moved-module calculation supplies the literal C.2.7
fixed-space conclusion, removing the remaining parabolic premise in both
degrees. Nonsingular control and the earlier degree-five closure result now
retain only the ordinary J4 component exclusion.

Apply the completed pure-point family next, followed by degree-four closure.
The resulting original three conclusions retain J4 exclusion and, only in
degree four, the original marked MS fixed-subgroup premise. J4 remains with
qt-d-double-natural-centralizers; the marked premise retains its producers
qt-d-double-natural-pure-fusion and qt-rank-two-ms93. Final discharge remains
with this task and qt-d-1222-double-natural. No conditional theorem here is
asserted to complete their original source theorem.
Source: Aschbacher--Smith 12.1.1--7, printed pp.788--792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both source degrees now need only the ordinary J4 component exclusion
for nonsingular control and the earlier degree-five weak-closure conclusion. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_middle_flag_of_many h hmany B hj
  intro hn S w hw _ _ _ Q K hKn hRK hi _ _ _ _ _
  subst n
  exact D.doubleNatural_four_adapted_C27_fixed h B S w hw K hKn hRK.le hi

/-- Apply nonsingular control, then the pure-point family, then degree-four
closure, retaining exactly J4 exclusion and the original marked MS premise. -/
theorem doubleNatural_conclusions_of_jankoFour_of_omega_fixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (n = 4 → ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    B.NonsingularCentralizers ∧ B.PureIntersectionCentralizes ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hj hfixed
  obtain ⟨hc,_,hw⟩ := D.doubleNatural_nonsingular_controls_of_jankoFour_of_many h hmany B hj
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  have hp := D.doubleNatural_pure_conclusions_of_many_of_omega_fixed
    h hmany B hw S hc (fun hn => hfixed hn S)
  exact ⟨hc,hp.2.2.2.2.2,
    (D.doubled_zeroClosure_of_controls_of_many h hmany B hc hp.2.2.2.2.2).2⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
