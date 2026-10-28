module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneUnitaryParameters
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneUnitaryCartan

/-!
# Unitary Cartan control on the original chosen quotient action

The original L/O₂(L) central quotient is identified with the selected
unitary model. Faithful descent of its automorphisms proves the weak Cartan
bound n' ≤ 2s. Together with the existing original-action generation
comparison, this removes the Cartan premise from the final exclusion.

The sole remaining premise is the genuine SQTK-dependent odd-prime
movement estimate of H.2. Its discharge and final unconditional exclusion
remain with qt-d-1222-nonmathieu-unitary-suzuki-exclusion.
Source: Aschbacher--Smith H.2 and 7.3.4--7.5.2, printed pp.378,699--700.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The sufficient Cartan estimate on the literal L/O₂(L) quotient action. -/
theorem sourceOrbit_unitary_cartan_bound
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s)) :
    nPrime (normalizerPCoreQuotientAction L).range ≤ 2*s := by
  let := h.toHypothesis1221.quasisimple
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hq
  exact unitary_centralCover_cartan_bound J hs2 hcard hconj
    ((D.orbitCentralQuotientEquiv h.toHypothesis1221).trans e) _

/-- All unitary endgame premises except H.2's ambient odd-prime estimate
have been discharged on the original action. -/
theorem sourceOrbit_unitary_excluded_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 4*s ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) : False :=
  D.sourceOrbit_unitary_excluded_of_model_estimates h hmany hV hs hnm hnon hs2 hq
    (D.sourceOrbit_unitary_cartan_bound h hs2 hq) hodd
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
