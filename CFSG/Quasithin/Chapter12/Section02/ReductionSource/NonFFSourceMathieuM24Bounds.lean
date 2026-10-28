module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuCocodeBounds
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuNearOffenders
public import CFSG.Quasithin.Chapter8.Section01

/-!
# The stronger M24 cocode bound on the original chosen orbit

The concrete near-offender theorem and odd-prime avoidance bound discharge
both local-action premises in the actual E.6.27 application. Assuming the
preceding source 8.1.1 containment for distinguished vectors, every escaping
subspace has rank at most three, hence r>=8. The fundamental weak-closure
inequality then gives r=8,w=2, offender-image rank six and kernel rank three;
every original outside overgroup has generation parameter two.

These are applications to the literal automizer, centralizers and minima.
The ambient pair-centralizer containment, remaining Mathieu branches and J4
recognition stay with qt-d-1222-nonff-mathieu. No unconditional 8.1.1 or final
recognition assertion is made here.
Source: Aschbacher--Smith 8.1.1--3, printed pp.712--714 (refs/quasithin.pdf).
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
/-- The exact source 8.1.2 M24 escaping bound, conditional only on the
preceding 8.1.1 distinguished-vector containment. Both local-action estimates
are proved on the full original automizer. The same owner retains 8.1.1. -/
theorem sourceOrbit_m24_escaping_rank_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) : rank U ≤ 3 := by
  by_contra hlarge
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have ha := markedSpace_avoids D.sourceOrbit U (normalizer (L : Set G)) E
    weightTwoOrbit hpair hescape
  obtain ⟨hn,hJ⟩ := m24_local_action_bounds D.sourceOrbit
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
    (h61.normal_in_localCentralizer hU hUW).1
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right a E hE ha (by omega)
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  exact hescape (source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide)
    (lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr) hn
    (le_inf ((ChapterB.thompsonJ_le _ _).trans inf_le_left) hJ)
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon))

/-- Source 8.1.1 now suffices for r≥8; no escaping-rank or numerical
callback remains in this original M24 application. -/
theorem sourceOrbit_m24_globalR_ge_eight_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) :
    8 ≤ globalR D.sourceOrbit := by
  have hd : rank D.sourceOrbit = 11 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_cocode)
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV (by omega : 8 ≤ rank D.sourceOrbit)
  intro U hUW hU hescape
  have hr := D.sourceOrbit_m24_escaping_rank_of_pair_control h hmany hV hq hnon a E hE hpair hU hUW hescape
  omega

/-- The numerical equality row in source 8.1.3 on the original chosen orbit.
The only preceding source premise retained is 8.1.1 pair control. -/
theorem sourceOrbit_m24_cocode_equalities_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    globalR D.sourceOrbit = 8 ∧ globalW D.sourceOrbit (T : Subgroup G) = 2 ∧
      rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 6 ∧
      rank (offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G)) = 3 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  exact Chapter8.m24_row_equalities D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)) hg
    (D.sourceOrbit_m24_globalR_ge_eight_of_pair_control h hmany hV hq hnon a E hE hpair)
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)
    (D.sourceOrbit_m24_automizer_twoRank_le_six h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq)
    ((Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_cocode))

/-- The finite minimum is attained by an actual original w-offender. Its
image and full action kernel have the source equality-row ranks. -/
theorem sourceOrbit_m24_cocode_offender_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      globalR D.sourceOrbit = 8 ∧ globalW D.sourceOrbit (T : Subgroup G) = 2 ∧
      rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 6 ∧
      rank (offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G)) = 3 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  have hw := D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup
    (ne_top_of_le_ne_top (by simp) hw)
  exact ⟨g,hg,D.sourceOrbit_m24_cocode_equalities_of_pair_control
    h hmany hV hq hnon a E hE hpair hg⟩

/-- Every original outside overgroup has generation parameter exactly two
in the M24 equality row. -/
theorem sourceOrbit_m24_generation_eq_two_of_pair_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (hpair : ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    generationParameter H = 2 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  obtain ⟨g,hg,hr,hw,himage,hkernel⟩ := D.sourceOrbit_m24_cocode_offender_of_pair_control
    h hmany hV hq hnon a E hE hpair
  obtain ⟨hl,hu,_⟩ := D.sourceOrbit_mathieu_generation_bounds h hmany hV hm hnon hH
  rw [hw] at hl
  have hl' : 2 ≤ generationParameter H := by exact_mod_cast hl
  exact le_antisymm hu hl'

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
