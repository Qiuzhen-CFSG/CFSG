module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuParameters

public import Theory.GroupTheory.SolvableRadical.AbelianCharacteristic.Elementary

/-!
# Odd-normalizer control for the normalized Mathieu orbit

For an odd actor fixing the original orbit, failure of fixed-residual
uniqueness gives the original pushing-up J₄ component. The proved cubic,
full-core and small-Mathieu comparisons exclude it, preserving the actual
component and its covering center. In the unique-residual branch the normal
component comparison excludes both the ordinary and cubic odd-local cases.
A characteristic elementary subgroup then extends the result to every
nontrivial odd subgroup of the literal relative centralizer.

This discharges the odd-normalizer premise of E.6.27 in the Mathieu
escaping-space argument. The numerical local-action estimates and final
Mathieu/J₄ assembly remain with this task.
Source: Aschbacher--Smith 4.4.3,7.4.1 and E.6.27, printed pp.623,700,257.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual fixed residual has unique maximal two-local overgroup N_G(L).
No Hall, abelianness or Sylow-permutation premise is required. -/
theorem sourceOrbit_mathieu_oddActor_residual_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  classical
  by_contra hnot
  have hc := D.sourceOrbit_mathieu_pushingUp_janko h hmany hV hnon hm A hAN hcomm ho hAV hnot
  have hci := mathieu_pushingUp_janko_inner hc
  have hfull := mathieu_pushingUp_full_cubic hci
  have hplaced := D.sourceOrbit_mathieu_pushingUp_cubic_placement h.toHypothesis1221 hm hfull
  have hambient := pushingUp_cubic_ambient h.simpleQTKE hplaced
  have hcent := D.sourceOrbit_mathieu_pushingUp_centralized_cubic h hmany hV hm hnon hambient
  have hcomp := pushingUp_cubic_ambient_component hcent
  have hquot := pushingUp_cubic_quotient_action hcomp
  have hnormal := pushingUp_full_cubic_resolution hquot
  have hdispl := D.pushingUp_core_displacement h hmany hV hm hnon hnormal
  have htriv := D.pushingUp_trivial_displacement h hmany hV hm hnon hdispl
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hfactor := D.pushingUp_core_factorization h.toHypothesis1221 hV hm hfix htriv
  have hgap := D.pushingUp_component_factor_gap h.toHypothesis1221 hV hm hfix hfactor
  have hsmall := D.sourceOrbit_pushingUp_factor_gap_small_mathieu h.toHypothesis1221 hfix hm hgap
  obtain ⟨J,H,W,hw,_,K,hK,_,_,_,_,⟨e⟩⟩ := hc
  rcases hsmall with h12 | h22
  · exact D.sourceOrbit_pushingUp_m12_false h hmany hV h12 hnon hw K hK e
  · exact D.sourceOrbit_pushingUp_m22_false h hmany hV h22 hnon hw K hK e

/-- Every nontrivial elementary odd subgroup fixing the source orbit has
its entire ambient normalizer inside the original N_G(L). -/
theorem sourceOrbit_mathieu_elementary_odd_normalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {p : ℕ} (hp : p.Prime) (hop : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (he : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G)) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let := he
  let := D.elementary
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact hop.pow
  let := h.quasisimple
  have hsect : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    apply NormalizedRankOneOddControl.relative_module_centralizer_le_sectionCentralizer L V D.normalizes
      _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hAL := hA.trans hsect
  obtain ⟨hAN,hcomm⟩ := (le_sectionCentralizer_iff A L).mp hAL
  have hAV := hA.trans inf_le_right
  have hu := D.sourceOrbit_mathieu_oddActor_residual_unique h hmany hV hm hnon A hAN hcomm ho hAV
  by_contra hout
  have hc := D.sourceOrbit_mathieu_normal_component_of_unique h.toHypothesis1221 hV hm
    A hne hA ho hu hout
  have hrows := D.sourceOrbit_mathieu_component_rows h.toHypothesis1221 hV hm A hAN hcomm ho hAV hc
  have hj := D.sourceOrbit_mathieu_janko_component h.toHypothesis1221 hm A hAN hcomm ho hAV hrows
  have ha := mathieu_janko_action (IsElementaryAbelian.isPGroup 2 V) ho hj
  have hr := mathieu_janko_fixed_residual h.simpleQTKE T.isPGroup'
    (hV.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes) D.elementary D.ne_bot ha
  have hs := mathieu_janko_fixed_residual_seed hr
  rcases D.sourceOrbit_mathieu_janko_comparison_or_cubic_section h.toHypothesis1221 hp hop
    A hne he hAL hAV hs with hcomp | ⟨_,hcubic⟩
  · have hcore := D.sourceOrbit_mathieu_compared_residual_core h hmany hV hm hnon hcomp
    exact D.sourceOrbit_no_core_compared_residual h.toHypothesis1221 hV hAN hcomm ho hAV hcore
  · have hcent := mathieu_janko_cubic_central_seed h.toHypothesis1221 hcubic
    have hrep := mathieu_janko_cubic_replacement h.toHypothesis1221 hcent
    have hcover := mathieu_janko_cubic_covered_replacement hrep
    have hfull := mathieu_janko_cubic_full_core h.toHypothesis1221 hcover
    have hfirst := mathieu_janko_cubic_first_row h.toHypothesis1221 hfull
    exact mathieu_janko_cubic_first_row_impossible hfirst

/-- Normalized 4.4.3 for every nontrivial odd subgroup of the literal
relative centralizer. A characteristic elementary subgroup preserves its
ambient normalizer, so no abelian or elementary hypothesis remains. -/
theorem sourceOrbit_mathieu_odd_normalizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card X)) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  let : Group.IsSolvable X := odd_order_theorem X ho
  obtain ⟨B,hBchar,hBcomm,hB⟩ := Group.exists_nontrivial_abelian_characteristic X
  let := hBchar
  let := hBcomm
  obtain ⟨p,hp,E,_,hEchar,hEelem,hE⟩ := B.exists_elementaryAbelian_characteristic_le hB
  let := hEchar
  let := hEelem
  let : Fact p.Prime := ⟨hp⟩
  have hoddE : Odd (Nat.card E) := ho.of_dvd_nat E.card_subgroup_dvd_card
  have hop : Odd p := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hn0
      have hcard := (one_lt_card_iff_ne_bot E).mpr hE
      rw [hn,hn0,pow_zero] at hcard
      omega
    exact hoddE.of_dvd_nat (hn.symm ▸ dvd_pow_self p hn0)
  have hEm : E.map X.subtype ≠ ⊥ := by
    intro hb
    exact hE ((E.map_eq_bot_iff_of_injective X.subtype_injective).mp hb)
  have hEA : E.map X.subtype ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
    rw [hV]
    exact (map_subtype_le E).trans hX
  have hEn := D.sourceOrbit_mathieu_elementary_odd_normalizer_le h hmany hV hm hnon
    hp hop (E.map X.subtype) hEm (IsElementaryAbelian.map X.subtype) hEA
  exact (normalizer_le_normalizer_characteristic_image X E).trans hEn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
