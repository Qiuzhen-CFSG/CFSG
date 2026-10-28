module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveEndpointStar
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveRankTwoStarSource

/-!
# Applying the degree-five endpoint geometry to the original centralizer

Both doubled-natural degrees now have SL5(2) as their literal star group
and a full component Sylow inside the star intersection. In degree five,
that intersection is an actual endpoint parabolic under every supplied
SL5(2) marking. These are proved source consequences, rather than extra
placement assumptions.

The endpoint point-action exclusion, degree-four fixed-space conclusion
and ordinary J4 exclusion remain with qt-d-double-natural-centralizers.
Pure fusion and corrected MS retain their existing producers and final
discharge at qt-d-1222-double-natural. The theorem applies the new geometry
to nonsingular centralizers, the global-r bound and degree-five zeroth
closure without claiming those unresolved source obligations are proved.
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
theorem doubleNatural_nonsingular_controls_of_jankoFour_endpoint_stars_of_many
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
        (∃ P : Sylow 2 (starImage K Q K), (P : Subgroup (starImage K Q K)) ≤
          (starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)) →
        (n = 5 → ∀ e : starImage K Q K ≃* BinaryLinear.OuterCyclic.LinearGroup 5,
          ∃ (b : BinaryLinear.FiveFlagGeometry.FiveBasis) (i : Fin 4),
            (i = 0 ∨ i = 3) ∧
            ((starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)).map
              e.toMonoidHom = BinaryLinear.FiveFlagGeometry.flagStabilizer b {i}) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_binaryFive_star_of_many h hmany B hj
  intro S w hw hc hn hout Q K hKn hRK hi hk ho hAn hAq he
  apply hp S w hw hc hn hout K hKn hRK hi hk ho hAn hAq he
  · rcases B.degree with hn | hn
    · subst n
      exact D.doubleNatural_four_adapted_C27_star_sylow h B S w hw K hKn hi
    · subst n
      exact D.doubleNatural_five_adapted_C27_star_sylow h B S w hw K hRK.le hi
  · intro hn
    subst n
    exact D.doubleNatural_five_adapted_C27_endpoint h B S w hw K hRK.le hi
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
