module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeAvoidance

/-!
# The cocode avoidance argument on the original chosen orbit

For M23 the concrete near-offender and odd-prime calculations discharge
both local-action premises of E.6.27 at every pair-avoiding subspace of
rank greater than four. Thus the distinguished-vector containment of
8.1.1 implies the escaping-rank bound four, then r >= 7, contradicting
the proved upper bound six. Under the original hypotheses this selects
an actual distinguished vector with escaping ambient centralizer,
retaining its M22 two-core quotient and full residual displacement.

For M24 the same literal application discharges the odd-prime alternative
and forces the higher Thompson subgroup to move the orbit whenever a
pair-avoiding subspace of rank at least four has escaping centralizer.

These results do not prove 8.1.1 or the unconditional Mathieu exclusion.
The original pushing-up construction and exclusion, remaining Mathieu
rows and final ambient J4 recognition remain with the consolidated
normalized Mathieu assembly owner, qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith, 8.1.1--3, printed pp.712--714, and E.6.27,
printed p.257 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuAvoidance
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The exact source 8.1.2 M23 escaping bound, conditional only on the
preceding 8.1.1 distinguished-vector containment. Both local-action estimates
are proved on the full original automizer. The same owner retains 8.1.1. -/
theorem sourceOrbit_m23_escaping_rank_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M23)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      m23CocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) : rank U ≤ 4 := by
  by_contra hlarge
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inl hq))
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have ha := markedSpace_avoids D.sourceOrbit U (normalizer (L : Set G)) E
    m23WeightTwoOrbit hpair hescape
  obtain ⟨hn,hJ⟩ := m23_local_action_bounds D.sourceOrbit
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
    (h61.normal_in_localCentralizer hU hUW).1
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right a E hE ha (by omega)
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  exact hescape (source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide)
    (lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr) hn
    (le_inf ((ChapterB.thompsonJ_le _ _).trans inf_le_left) hJ)
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon))

/-- Source 8.1.1 now suffices for r≥7; no escaping-rank or numerical
callback remains in this original M23 application. -/
theorem sourceOrbit_m23_globalR_ge_seven_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M23)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      m23CocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) :
    7 ≤ globalR D.sourceOrbit := by
  have hd : rank D.sourceOrbit = 11 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_cocode)
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV (by omega : 7 ≤ rank D.sourceOrbit)
  intro U hUW hU hescape
  have hr := D.sourceOrbit_m23_escaping_rank_of_pair_control h hmany hV hq hnon a E hE hpair hU hUW hescape
  omega

/-- The M23 source branch is excluded once 8.1.1 is supplied, because its
proved lower bound seven contradicts the actual FWCI upper bound six. -/
theorem sourceOrbit_m23_false_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M23)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      m23CocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) : False := by
  have hh := (D.sourceOrbit_m23_globalR_ge_seven_of_pair_control h hmany hV hq hnon a E hE hpair).trans
    (D.sourceOrbit_m23_globalR_le_six h hmany hV hq hnon)
  norm_num at hh

/-- Under the original M23 hypotheses, all remaining work is concentrated
at an actual distinguished vector with escaping ambient centralizer. Its
literal M22 quotient and full residual displacement are retained. -/
theorem sourceOrbit_m23_escaping_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M23,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          m23CocodeRepresentation (a b) (E v)) ∧
        ∃ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit ∧
          ¬ centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) ∧
          Nonempty (((L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ⧸
            pCore 2 (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) ≃* M22) ∧
          ⁅D.sourceOrbit, (solvableResidual
            (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
              (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  classical
  obtain ⟨a,E,hE,hpairs⟩ := D.sourceOrbit_m23_pair_quotients_of_many h hmany hV hq hnon
  have hex : ∃ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit ∧
      ¬ centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
    by_contra! hn
    exact D.sourceOrbit_m23_false_of_pair_control h hmany hV hq hnon a E hE hn
  obtain ⟨x,hx,hout⟩ := hex
  exact ⟨a,E,hE,x,hx,hout,hpairs x hx⟩

/-- In the M24 cocode row, an escaping subspace of rank at least four
which avoids the pair orbit forces a moving higher-Thompson generator.
The odd-element alternative of 8.1.2 is fully discharged. -/
theorem sourceOrbit_m24_escaping_thompson_moves
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G))
    (ha : Disjoint (markedSpace D.sourceOrbit U E : Set Cocode) weightTwoOrbit)
    (hrank : 3 < rank U) :
    ¬ ChapterB.thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      centralizer (D.sourceOrbit : Set G) := by
  intro hJ
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have hn := m24_local_cartan_bound D.sourceOrbit
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right a E hE ha hrank
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  exact hescape (source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide)
    (lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr) hn
    (le_inf ((ChapterB.thompsonJ_le _ _).trans inf_le_left) hJ)
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
