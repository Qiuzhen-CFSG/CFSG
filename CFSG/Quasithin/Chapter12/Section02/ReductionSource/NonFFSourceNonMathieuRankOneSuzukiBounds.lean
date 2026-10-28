module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneGeneration
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension

/-!
# Ambient Suzuki bounds from the two remaining model estimates

The odd-prime displacement bound excludes nontrivial Cartan witnesses in
small-subspace centralizers. The completed higher-Thompson and odd-local
arguments then apply E.6.27. Taking the actual globalR minimum gives the
unrounded bound 8n <= 3r. The literal quotient-action Cartan estimate supplies
w <= n, and the original weak-closure inequality gives the contradiction.

The two model estimates remain explicit and unproved here. Their discharge,
the unitary estimates and both unconditional selected-family exclusions stay
with qt-d-1222-nonmathieu-unitary-suzuki-exclusion. No new ambient premise is
introduced, and no conditional conclusion is advertised as source 7.5.2.
Source: Aschbacher--Smith H.3, 7.3.4, 7.4.1 and 7.5.2,
printed pp.379,699--700.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- E.6.27 gives the full centralizer bound from the remaining H.3 estimate. -/
theorem sourceOrbit_suzuki_small_corank_centralizer_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 8 * (2 * m + 1) ≤
        3 * fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hc : 3 * subgroupCorank D.sourceOrbit U < 8 * (2 * m + 1)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  apply D.sourceOrbit_suzuki_centralizer_le_of_nPrime h hmany hV hs hnm hnon hm e hU hUW
  exact induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right hodd hc

/-- The exact unrounded 7.4 bound, conditional only on the odd-prime model
calculation; all ambient centralizer and minimum arguments are proved. -/
theorem sourceOrbit_suzuki_globalR_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 8 * (2 * m + 1) ≤
        3 * fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) :
    ((8 * (2 * m + 1) : ℕ) : ℕ∞) ≤ 3 * globalR D.sourceOrbit := by
  by_cases ht : globalR D.sourceOrbit = ⊤
  · simp [ht]
  obtain ⟨U,hUW,hescape,hcor⟩ := globalR_attained ht
  rw [← hcor]
  change ((8 * (2 * m + 1) : ℕ) : ℕ∞) ≤
    ((3 * subgroupCorank D.sourceOrbit U : ℕ) : ℕ∞)
  apply ENat.natCast_le_natCast.mpr
  by_contra hn
  have hc : 3 * subgroupCorank D.sourceOrbit U < 8 * (2 * m + 1) := by omega
  have hU : U ≠ ⊥ := by
    intro hz
    obtain ⟨_,_,hd⟩ := D.sourceOrbit_suzuki_model hs hm e
    rw [hz, corank_bot, hd] at hc
    omega
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  exact hescape ((h61.centralizer_le_iff hU hUW).mp
    (D.sourceOrbit_suzuki_small_corank_centralizer_of_odd_fixedCodim
      h hmany hV hs hnm hnon hm e hodd hU hUW hc))

/-- Literal chosen-module application of 7.5.2 once both remaining model
estimates have been supplied by this task's final assembly. -/
theorem sourceOrbit_suzuki_excluded_of_model_estimates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hcartan : nPrime (normalizerPCoreQuotientAction L).range ≤ 2 * m + 1)
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 8 * (2 * m + 1) ≤
        3 * fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) : False := by
  exact Chapter7.suzuki_parameter_contradiction (n := 2 * m + 1) D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) (by omega)
    (D.sourceOrbit_suzuki_automizer_rank h hs hm e)
    (D.sourceOrbit_suzuki_globalW_le_of_cartan_bound h hmany hV hs hnm hnon hm e hcartan)
    (D.sourceOrbit_suzuki_globalR_of_odd_fixedCodim h hmany hV hs hnm hnon hm e hodd)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
