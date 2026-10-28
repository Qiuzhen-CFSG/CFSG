module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.FixedSpanApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.OddSpace
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.NearAvoidance

/-!
# Original M22 cocode exclusion from distinguished-point control

The native near-offender avoidance calculation and odd displacement bound
supply both local-action premises of E.6.27. Thus source 8.1.1 point control
implies that an escaping subgroup has rank at most four and the original
r is at least six. The complete literal fixed-span calculation contradicts
this. Every module, component, full automizer and covering kernel is the
original one.

Only the preceding ambient distinguished-point containment remains explicit.
This is not the unconditional row exclusion or final M24 cocode selection.
Source: Aschbacher--Smith 8.1.1--3, pp.712--714, refs/quasithin.pdf.
-/
public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuShadowRows
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual escaping-space bound, with only source 8.1.1 retained. -/
theorem sourceOrbit_m22_cocode_escaping_rank_of_point_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCocodeRepresentation)
    (hpoint : ∀ x : D.sourceOrbit,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) (Additive.ofMul x) ∈
        m22WeightTwoFamily → centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) : rank U ≤ 4 := by
  by_contra hlarge
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have ha := markedCocodeSpace_avoids D.sourceOrbit U (normalizer (L : Set G)) E hpoint hescape
  obtain ⟨a,hinj,hE,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h.toHypothesis1221 d
  have hJ := cocode_local_thompson_bound D.sourceOrbit
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
    (h61.normal_in_localCentralizer hU hUW).1
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right a hinj E hE ha (by omega)
  have hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) := by
    let := m22_isSimpleGroup
    have hz : center D.orbitComponent = ⊥ := by
      have hh := FixedElementary.map_center d.componentEquiv
      rw [m22_center_eq_bot] at hh
      exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans d.componentEquiv⟩
  have hn := D.sourceOrbit_m22_large_local_nPrime_le_one h hmany hV hq hnon hU hUW (by omega)
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  exact hescape (source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide)
    (lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr) hn
    (le_inf ((ChapterB.thompsonJ_le _ _).trans inf_le_left) hJ)
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon))

/-- Original point containment forces the required r≥6, without a numerical
or near-offender premise. -/
theorem sourceOrbit_m22_cocode_globalR_ge_six_of_point_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCocodeRepresentation)
    (hpoint : ∀ x : D.sourceOrbit,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) (Additive.ofMul x) ∈
        m22WeightTwoFamily → centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) :
    6 ≤ globalR D.sourceOrbit := by
  have hd : rank D.sourceOrbit = 10 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans
      ((D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv).finrank_eq.trans finrank_m22Cocode)
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV (by omega : 6 ≤ rank D.sourceOrbit)
  intro U hUW hU hescape
  have hr := D.sourceOrbit_m22_cocode_escaping_rank_of_point_control h hmany hV hm hnon d hpoint hU hUW hescape
  omega

/-- Source 8.1.1 is the only remaining earlier premise of the original M22
cocode exclusion; the near-offender and both fixed-span estimates are proved. -/
theorem sourceOrbit_not_m22_cocode_of_point_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCocodeRepresentation)
    (hpoint : ∀ x : D.sourceOrbit,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) (Additive.ofMul x) ∈
        m22WeightTwoFamily → centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) : False :=
  D.sourceOrbit_not_m22_cocode_of_six_le_globalR h hmany hV hm hnon d
    (D.sourceOrbit_m22_cocode_globalR_ge_six_of_point_control h hmany hV hm hnon d hpoint)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
