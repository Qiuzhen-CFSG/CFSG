module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.CodeNearBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeHeldExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.OddSpace
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PairRanks
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# The original M22-code weak closure and geometric pair

The native near-offender displacement bound forces higher Thompson
centralization for every local action fixing a subspace of rank greater than
four. The actual odd-normalizer and odd-displacement bounds then apply E.6.27
to escaping subspaces, giving r ≥ 6. The fundamental weak-closure inequality
and the full automizer's rank-five bound give positive w. Together with the
proved H-star two-core escape this constructs the original geometric pair,
with its full two-core quotient and internal conjugator retained. Its degree
is one or two; degree-two exclusion and the later source argument remain.

The private import continues the existing pair implementation: only its
generic normalizer and restricted quadratic-ratio proofs are used.
Source: Aschbacher--Smith 7.5.6(1),8.2.2--3,H.16.5, printed pp.702,714--716,404,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuShadowRows
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
private theorem code_component_quotient
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) := by
  let := m22_isSimpleGroup
  have hz : center D.orbitComponent = ⊥ := by
    have hh := FixedElementary.map_center d.componentEquiv
    rw [m22_center_eq_bot] at hh
    exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans d.componentEquiv⟩

/-- Every escaping subspace of the original code orbit has rank at most four. -/
theorem sourceOrbit_m22_code_escaping_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) : rank U ≤ 4 := by
  by_contra hlarge
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  have hJ := code_local_thompson_bound D.sourceOrbit
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
    (h61.normal_in_localCentralizer hU hUW).1
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right a hinj E hE (by omega)
  have hq := D.code_component_quotient d
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inl hq)
  have hn := D.sourceOrbit_m22_large_local_nPrime_le_one h hmany hV hq hnon hU hUW (by omega)
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  exact hescape (source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide)
    (lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr) hn
    (le_inf ((ChapterB.thompsonJ_le _ _).trans inf_le_left) hJ)
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon))

/-- The original M22-code row has r ≥ 6, with no extra local-action premise. -/
theorem sourceOrbit_m22_code_globalR_ge_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) :
    6 ≤ globalR D.sourceOrbit := by
  have hd : rank D.sourceOrbit = 10 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans
      ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv).finrank_eq.trans finrank_m22Code)
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV (by omega : 6 ≤ rank D.sourceOrbit)
  intro U hUW hU hescape
  have hr := D.sourceOrbit_m22_code_escaping_rank h hmany hV hnon d hU hUW hescape
  omega

/-- Source 7.5.6(1) on the same original M22-code module and Sylow. -/
theorem sourceOrbit_m22_code_globalW_pos
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) :
    0 < globalW D.sourceOrbit (T : Subgroup G) := by
  have hr := D.sourceOrbit_m22_code_globalR_ge_six h hmany hV hnon d
  have ha := D.sourceOrbit_m22_automizer_twoRank_le_five h hmany hV (D.code_component_quotient d) hnon
  apply globalW_pos_of_fwci_gap D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
  exact lt_of_le_of_lt (ENat.natCast_le_natCast.mpr ha)
    (lt_of_lt_of_le (by decide : (5 : ℕ∞) < 6) hr)

/-- The literal original M22-code pair has degree one or two. This constructs
its actors and covering quotient rather than assuming pair data. -/
theorem sourceOrbit_m22_code_geometric_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧ (k = 1 ∨ k = 2) := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  obtain ⟨R,hR,n,⟨w⟩⟩ := exists_original_witness_of_positive_weak_closure h28 hfit
    (D.m24_hstar_normalizes h hmany hV hnon hH)
    (D.sourceOrbit_m22_code_globalW_pos h hmany hV hnon d)
  obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h28 hfit R hR w
    (D.m24_restricted_quadraticRatio h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  have ha := D.sourceOrbit_m22_automizer_twoRank_le_five h hmany hV (D.code_component_quotient d) hnon
  exact ⟨I,w.degree,i,S,s,s.parameter_one_or_two_of_rank_five ha⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
