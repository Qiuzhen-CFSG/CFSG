module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveRankTwoStar
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourLinearStarSource

/-!
# The binary-five star reduction in both doubled-natural degrees

The literal C.2.7 star group is SL5(2) in both degrees. In degree five,
the perfect residual's cubic rank excludes all remaining rank-two rows;
the previously checked degree-four argument excludes SL4(2).

The theorem below feeds these reductions to nonsingular centralizer control,
the global-r bound and degree-five zeroth closure. It retains the original
radical, star map, relative normality and fixed-space conclusion. The SL5(2)
parabolic argument and ordinary J4 exclusion still belong to this task.
Pure fusion and corrected MS retain their existing producers and final
discharge at qt-d-1222-double-natural. This is not the full source theorem.
Source: Aschbacher--Smith 12.1.1--3, printed pp.788--790.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the binary-five star reduction in both degrees to the original nonsingular-centralizer
and degree-five closure conclusions. The J4 and remaining parabolic premises
retain their final discharge with this task; no universal C.2.7 Source is assumed. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_binaryFive_star_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal →
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) →
        Nonempty (starImage K Q K ≃* SL(5,ZMod 2)) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_C27_of_many h hmany B hj
  intro S w hw hc hn hout Q K hKn hRK hi hk ho hAn hAq
  apply hp S w hw hc hn hout K hKn hRK hi hk ho hAn hAq
  rcases B.degree with hn | hn
  · subst n
    exact D.doubleNatural_four_adapted_C27_star_linearFive h B S w hw K hKn hRK.le hi
  · subst n
    exact D.doubleNatural_five_adapted_C27_star_linearFive h B S w hw K hRK.le hi
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
