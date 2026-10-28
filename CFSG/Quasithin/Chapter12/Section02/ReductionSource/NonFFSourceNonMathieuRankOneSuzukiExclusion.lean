module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSuzukiDisplacement

/-!
# Excluding the original Suzuki orbit

Central-quotient descent applies the Cartan estimate to the literal
normalizer action on L/O₂(L). Hall faithfulness and the ambient generation
comparison give w <= n. Together with the proved automizer rank and
small-corank centralizer estimate, this gives 8n <= 3r <= 6n, a contradiction.
All odd-local, reciprocal-escape, Held-cover and displacement inputs are
proved upstream. The action, chosen orbit and original Sylow are unchanged.

Source: Aschbacher--Smith 7.2.1, 7.3.4, 7.4.1 and 7.5.2,
printed pp.698--700.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The Cartan estimate for the literal conjugation action on L/O₂(L). -/
theorem sourceOrbit_suzuki_cartan_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    nPrime (normalizerPCoreQuotientAction L).range ≤ 2*m+1 := by
  let := h.toHypothesis1221.quasisimple
  exact suzuki_centralCover_cartan_bound hm
    ((D.orbitCentralQuotientEquiv h.toHypothesis1221).trans e) _
    (MathieuGeneration.inner_le_quotientAction_range L)

/-- The upper w-column in the Suzuki row, on the unchanged orbit and Sylow. -/
theorem sourceOrbit_suzuki_globalW_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    globalW D.sourceOrbit T ≤ (2*m+1 : ℕ) :=
  D.sourceOrbit_suzuki_globalW_le_of_cartan_bound h hmany hV hs hnm hnon hm e
    (D.sourceOrbit_suzuki_cartan_bound h hm e)

/-- All three source parameters in the selected Suzuki row. -/
theorem sourceOrbit_suzuki_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    primeRank 2 (Automizer D.sourceOrbit) ≤ 2*m+1 ∧
    globalW D.sourceOrbit T ≤ (2*m+1 : ℕ) ∧
    ((8*(2*m+1) : ℕ) : ℕ∞) ≤ 3*globalR D.sourceOrbit :=
  ⟨D.sourceOrbit_suzuki_automizer_rank h hs hm e,
    D.sourceOrbit_suzuki_globalW_le h hmany hV hs hnm hnon hm e,
    D.sourceOrbit_suzuki_globalR h hmany hV hs hnm hnon hm e⟩

/-- Source 7.5.2 excludes the selected Suzuki quotient, with every model,
odd-local and ambient parameter premise discharged. -/
theorem sourceOrbit_suzuki_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) : False := by
  obtain ⟨hq,hw,hr⟩ := D.sourceOrbit_suzuki_parameters h hmany hV hs hnm hnon hm e
  exact Chapter7.suzuki_parameter_contradiction D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) (by omega) hq hw hr
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
