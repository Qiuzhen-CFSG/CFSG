module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSuzukiBounds
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddDisplacement

/-!
# The full ambient Suzuki lower bound for r

The literal automizer marking transports the proved H.3 odd-prime
displacement estimate. The existing E.6.27 application combines it with
higher-Thompson control, the initial E.6.3 estimate, and the completed
odd-local theorem to control every small-corank centralizer. Taking the
actual globalR minimum yields 8n <= 3r with no extra model premise.

The conditional exclusion now retains only the Cartan estimate for the
original quotient-conjugation image. That estimate, the unitary bounds,
and both final exclusions remain with the same assembly owner,
qt-d-1222-nonmathieu-unitary-suzuki-exclusion.
Source: Aschbacher--Smith, H.3, 7.4.1 and 7.5.2, printed pp.379,700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The H.3 odd-prime displacement bound on the literal ambient automizer. -/
theorem sourceOrbit_suzuki_odd_prime_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (a : Automizer D.sourceOrbit) (ha : orderOf a = p) :
    8 * (2*m+1) ≤ 3 * fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) := by
  obtain ⟨j,hj,hcoord⟩ := D.sourceOrbit_automizer_marking h.toHypothesis1221
  exact suzuki_odd_prime_fixedCodim_of_normalizer_marking hm (hs.suzukiModel hm e)
    (automizerRepresentation D.sourceOrbit) j hj D.sourceOrbitCoordinates hcoord hp ho a ha

/-- Source 7.4.1's small-corank centralizer conclusion for the selected Suzuki row. -/
theorem sourceOrbit_suzuki_small_corank_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hc : 3 * subgroupCorank D.sourceOrbit U < 8 * (2*m+1)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  D.sourceOrbit_suzuki_small_corank_centralizer_of_odd_fixedCodim h hmany hV hs hnm hnon hm e
    (D.sourceOrbit_suzuki_odd_prime_fixedCodim h hs hm e) hU hUW hc

/-- The full unrounded Suzuki r-bound, with all model and ambient inputs discharged. -/
theorem sourceOrbit_suzuki_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    ((8 * (2*m+1) : ℕ) : ℕ∞) ≤ 3 * globalR D.sourceOrbit :=
  D.sourceOrbit_suzuki_globalR_of_odd_fixedCodim h hmany hV hs hnm hnon hm e
    (D.sourceOrbit_suzuki_odd_prime_fixedCodim h hs hm e)

/-- The Suzuki exclusion now retains just the original-action Cartan bound.
Its discharge and the final unconditional exclusion remain with the same owner. -/
theorem sourceOrbit_suzuki_excluded_of_cartan_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hc : nPrime (normalizerPCoreQuotientAction L).range ≤ 2*m+1) : False :=
  D.sourceOrbit_suzuki_excluded_of_model_estimates h hmany hV hs hnm hnon hm e hc
    (D.sourceOrbit_suzuki_odd_prime_fixedCodim h hs hm e)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
