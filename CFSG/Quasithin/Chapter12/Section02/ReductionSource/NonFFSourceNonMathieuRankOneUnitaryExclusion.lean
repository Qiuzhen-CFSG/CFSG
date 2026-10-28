module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneUnitaryCartan
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneUnitaryDisplacement
/-!
# Excluding the original unitary chosen orbit

The normalizer of the nontrivial elementary chosen orbit is the actual SQTK
cover. Its literal automizer quotient, component surjection and coordinate
marking supply H.2 with no extra displacement premise. The existing E.6.27
application gives r >= 4s. The previously proved Cartan bound w <= 2s already
suffices: (s+1)+2s < 4s for s >= 2. Thus the original unitary row is excluded.
All original hypotheses, the Sylow subgroup, and both actions are retained.

Source: Aschbacher--Smith H.2, 7.2.1--7.5.2 and E.6.27,
printed pp.378,698--700,257.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The SQTK cover in H.2 is the actual original orbit normalizer. -/
theorem sourceOrbit_normalizer_sqtk
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (D.sourceOrbit : Set G)) :=
  h.simpleQTKE.twoLocal_sqtk ⟨D.sourceOrbit,D.sourceOrbit_weakClosure_setup.nontrivial,
    IsElementaryAbelian.isPGroup 2 D.sourceOrbit,rfl⟩

/-- The H.2 odd-prime displacement bound on the literal ambient automizer. -/
theorem sourceOrbit_unitary_odd_prime_fixedCodim
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (a : Automizer D.sourceOrbit) (ha : orderOf a = p) :
    4*s ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) := by
  obtain ⟨F,_,_,_,J,hcard,hconj,⟨M⟩,_⟩ := D.sourceOrbit_unitary_model hs hs2 hq
  obtain ⟨M₀⟩ := M.exists_standard (by omega) hcard hconj
  obtain ⟨j,hj,hjcoord⟩ := D.sourceOrbit_automizer_marking h
  exact unitary_odd_fixedCodim_of_ambient_marking M₀
    hs.faithful hs.irreducible rfl hs2 hcard hconj
    (automizerRepresentation D.sourceOrbit) j hj D.sourceOrbitCoordinates hjcoord
    D.sourceOrbit.normalizerMonoidHom.rangeRestrict
    D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
    D.orbitComponentHom D.orbitComponentHom_surjective
    (inclusion D.sourceOrbit_component_normalizes)
    D.sourceOrbitCoordinates_component_intertwines hp ho
    ((D.sourceOrbit_normalizer_sqtk h).stronglyQuasithin p hp ho) a ha

/-- The full unitary r-bound on the original chosen orbit. -/
theorem sourceOrbit_unitary_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s)) :
    ((4*s : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit :=
  D.sourceOrbit_unitary_globalR_of_odd_fixedCodim h hmany hV hs hnm hnon hs2 hq
    (D.sourceOrbit_unitary_odd_prime_fixedCodim h.toHypothesis1221 hs hs2 hq)

/-- The selected unitary row is impossible with the complete original source
hypotheses, original Sylow subgroup, and literal chosen-orbit action. -/
theorem sourceOrbit_unitary_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2^s)) : False :=
  D.sourceOrbit_unitary_excluded_of_odd_fixedCodim h hmany hV hs hnm hnon hs2 hq
    (D.sourceOrbit_unitary_odd_prime_fixedCodim h.toHypothesis1221 hs hs2 hq)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
