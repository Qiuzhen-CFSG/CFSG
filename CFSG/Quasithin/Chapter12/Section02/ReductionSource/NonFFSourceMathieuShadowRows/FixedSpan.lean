module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.MarkedFixedSpan

/-!
# Original M22 cocode offenders reduce to the outer rank-four case

The full original automizer marking and the weak-closure inequalities apply
the native fixed-span calculations to the chosen orbit. Assuming the earlier
source bound r ≥ 6, rank-five offenders are impossible. Rank four forces
r = 6 and w = 2, and the inner rank-four fixed-span bound then excludes
containment in the original component image.

The earlier bound r ≥ 6 remains an explicit premise: this application does
not claim original 8.1.2 or the full M22 cocode exclusion. The distinguished-point
centralizer argument and outer rank-four calculation remain with the same
shadow-row proof. Source: Aschbacher--Smith 8.1.2--3, printed pp.713--714,
refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- On the original M22 cocode orbit, the source bound r≥6 excludes rank
five and all inner rank-four offenders. The only remaining offenders have
r=6, w=2, rank four, and escape the original component image. -/
theorem sourceOrbit_m22_cocode_offender_reduction_of_six_le_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (hr : 6 ≤ globalR D.sourceOrbit)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    globalR D.sourceOrbit = 6 ∧ globalW D.sourceOrbit (T : Subgroup G) = 2 ∧
      rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 4 ∧
      ¬ inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g) ≤
        inducedAutomizer D.sourceOrbit L := by
  obtain ⟨a,ha,hE,hcomp,hpre,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h.toHypothesis1221 d
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have hm5 : primeRank 2 (Automizer D.sourceOrbit) ≤ 5 :=
    (_root_.primeRank_le_of_injective 2 (m22PairStabilizerEquivAut.toMonoidHom.comp a)
      (m22PairStabilizerEquivAut.injective.comp ha)).trans m22_automorphism_twoRank_le_five
  have hT := D.sourceOrbit_weakClosure_setup
  have h24 : HypothesisE324 D.sourceOrbit (T : Subgroup G) :=
    Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
  have hw := D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon
  obtain ⟨hwp,hwn,hrank,_⟩ := Chapter8.m22_corankFamily_image_ranks hT h24 hg hr hw hm5
  have hwr : globalW D.sourceOrbit (T : Subgroup G) < globalR D.sourceOrbit :=
    lt_of_le_of_lt hw (lt_of_lt_of_le (by decide : (2 : ℕ∞) < 6) hr)
  have hc := Chapter8.globalW_le_offenderCentralizerSpan_corank hT hg hwr
    (lt_of_lt_of_le (by decide : (5 : ℕ∞) < 6) hr)
  have hfour : rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 4 := by
    rcases hrank with hfour | hfive
    · exact hfour
    · have hs := Chapter8.MathieuShadowRows.marked_rank_five_span hg a ha E hE hfive hwp hwn
      rw [hs,subgroupCorank,relIndex_self,Nat.log_one_right] at hc
      have hz : (globalW D.sourceOrbit (T : Subgroup G)).toNat = 0 :=
        congrArg ENat.toNat (bot_unique hc)
      omega
  have hrf := ENat.natCast_toNat (globalR_ne_top_of_noncentralizing_conjugate g hg.1)
  have hwf := ENat.natCast_toNat hg.globalW_ne_top
  have hrn : 6 ≤ (globalR D.sourceOrbit).toNat := by rw [←hrf] at hr; exact_mod_cast hr
  have hi := (lemma_E_3_28 hT h24 hg).2.1.1
  rw [hfour,←hrf,←hwf] at hi
  have hin : (globalR D.sourceOrbit).toNat ≤
      (globalW D.sourceOrbit (T : Subgroup G)).toNat + 4 := by exact_mod_cast hi
  have hwe : (globalW D.sourceOrbit (T : Subgroup G)).toNat = 2 := by omega
  have hre : (globalR D.sourceOrbit).toNat = 6 := by omega
  have hw2 : globalW D.sourceOrbit (T : Subgroup G) = 2 := by simpa only [hwe, Nat.cast_ofNat] using hwf.symm
  refine ⟨by simpa only [hre, Nat.cast_ofNat] using hrf.symm,hw2,hfour,?_⟩
  intro hinner
  have hmarked : (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)).map a ≤
      m22ToPairStabilizer.range := by
    rintro _ ⟨b,hb,rfl⟩
    exact (show b ∈ m22ToPairStabilizer.range.comap a from hpre.symm ▸ hinner hb)
  have hb := Chapter8.MathieuShadowRows.marked_inner_rank_four_span hg a ha E hE
    hfour hwe hmarked
  rw [hw2] at hc
  have hc2 : 2 ≤ subgroupCorank D.sourceOrbit
      (Chapter8.offenderCentralizerSpan D.sourceOrbit g 5) := by exact_mod_cast hc
  omega
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
