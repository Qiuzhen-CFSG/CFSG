module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.FixedSpan
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.OuterFixedSpan

/-!
# The complete fixed-span contradiction on the original M22 cocode orbit

The native rank-four estimate covers inner and outer actors. Together with
the previously proved rank-five calculation, full-automizer marking and
full-kernel corank-family transport, it gives the literal contradiction in
original 8.1.3 as soon as the earlier bound r≥6 is supplied. Equivalently,
the original M22 cocode row has r≤5 under the initial source hypotheses.

This is not yet the M22 cocode exclusion: original 8.1.1--2 must supply the
opposite bound from distinguished-vector centralizers and escaping subspaces.
The M22-code and M24-code branches and final selection also remain open.
Source: Aschbacher--Smith 8.1.3, printed pp.713--714, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- All fixed-span premises in the original M22 cocode contradiction are
now discharged. Only the earlier escaping-space bound r≥6 is retained. -/
theorem sourceOrbit_not_m22_cocode_of_six_le_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (hr : 6 ≤ globalR D.sourceOrbit) : False := by
  have hw := D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon
  have hwfin : globalW D.sourceOrbit (T : Subgroup G) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hw
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top D.sourceOrbit_weakClosure_setup hwfin
  obtain ⟨_,hw2,hfour,_⟩ := D.sourceOrbit_m22_cocode_offender_reduction_of_six_le_globalR
    h hmany hV hm hnon d hr hg
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h.toHypothesis1221 d
  have hs := Chapter8.MathieuShadowRows.marked_rank_four_span hg a ha _ hE hfour
    (by rw [hw2]; rfl)
  have hlo := Chapter8.globalW_le_offenderCentralizerSpan_corank D.sourceOrbit_weakClosure_setup hg
    (lt_of_le_of_lt hw (lt_of_lt_of_le (by decide : (2 : ℕ∞) < 6) hr))
    (lt_of_lt_of_le (by decide : (5 : ℕ∞) < 6) hr)
  rw [hw2] at hlo
  have hlo' : 2 ≤ subgroupCorank D.sourceOrbit (Chapter8.offenderCentralizerSpan D.sourceOrbit g 5) := by
    exact_mod_cast hlo
  omega

/-- The original M22 cocode row satisfies r≤5. The missing source 8.1.2
lower bound, rather than any extra fixed-span assumption, will exclude it. -/
theorem sourceOrbit_m22_cocode_globalR_le_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation) : globalR D.sourceOrbit ≤ 5 := by
  have hn : ¬ 6 ≤ globalR D.sourceOrbit :=
    D.sourceOrbit_not_m22_cocode_of_six_le_globalR h hmany hV hm hnon d
  have hf : globalR D.sourceOrbit ≠ ⊤ := by intro he; apply hn; rw [he]; exact le_top
  have he := ENat.natCast_toNat hf
  have hr : (globalR D.sourceOrbit).toNat ≤ 5 := by
    by_contra! hl
    apply hn
    rw [←he]
    exact_mod_cast (show 6 ≤ (globalR D.sourceOrbit).toNat by omega)
  rw [←he]
  exact_mod_cast hr
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
