module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveStarExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveEndpointStarSource

/-!
# Removing the degree-five nonnormal branch from centralizer assembly

The original characteristic-two degree-five point residual is normal:
otherwise its containing C-component gives the now impossible C.2.7 star
input. The literal nonsingular-centralizer, global-r and zeroth-closure
consumer therefore needs only the J4 component exclusion in degree five.
For both degrees together, the remaining fixed-space premise is restricted
to degree four and retains the actual radical, star quotient and Sylow.

The J4 exclusion and degree-four parabolic argument remain with
qt-d-double-natural-centralizers. Pure fusion and corrected MS retain
their existing producers and final discharge at qt-d-1222-double-natural.
No degree-four weak-closure assertion is used in these earlier arguments.
Source: Aschbacher--Smith 12.1.1--3, printed pp.788--790.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Characteristic two forces normality of the original degree-five point residual. -/
theorem doubleNatural_five_adapted_residual_normal_of_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc
  by_contra hn
  obtain ⟨K,hKn,hRK,hi⟩ := D.doubleNatural_adapted_nonnormal_C27_input h B S w hw hc hn
  exact D.doubleNatural_five_adapted_C27_impossible h B S w hw K hKn hRK.le hi

/-- The only remaining parabolic fixed-space premise is in degree four. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_four_star_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (n = 4 → ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
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
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_endpoint_stars_of_many h hmany B hj
  intro S w hw hc hn hout Q K hKn hRK hi hk ho hAn hAq he hP _
  rcases B.degree with hn4 | hn5
  · exact hp hn4 S w hw hc hn hout K hKn hRK hi hk ho hAn hAq he hP
  · subst n
    exact (D.doubleNatural_five_adapted_C27_impossible h B S w hw K hKn hRK.le hi).elim

/-- In degree five only the actual ordinary J4 component exclusion remains
before nonsingular centralizer control and positive zeroth weak closure. -/
theorem doubleNatural_five_nonsingular_controls_of_jankoFour_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        8 ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    B.NonsingularCentralizers ∧
      (5 : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hj
  obtain ⟨hc,hr,hw⟩ := D.doubleNatural_nonsingular_controls_of_jankoFour_four_star_of_many
    h hmany B hj (fun hn => by omega)
  exact ⟨hc,hr,hw rfl⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
