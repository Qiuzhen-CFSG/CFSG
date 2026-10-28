module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeResidualEquality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeSelectedExclusion

/-!
# Exclusion of the original M22 code

The same supplied pair gives residual equality and Sylow normalization in
8.2.9. Its selected code coordinates then force the point closure and the
order-32 two-core with full alternating-six quotient excluded by the local
carrier theorem. Selecting the pair once gives the original orbit exclusion.
Source: Aschbacher--Smith 8.2.9--13, printed pp.720--723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original M22-code row is impossible for the supplied pair and
conjugator, without an additional normalization or kernel premise. -/
theorem sourceOrbit_m22_code_selected_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) : False := by
  obtain ⟨_,_,_,_,_,hTVA⟩ :=
    D.sourceOrbit_m22_code_selected_residual_equality h hmany hV hnon d hH s
  obtain ⟨hA,hAT,hfix,hker,hcent,hfive,hfour,_,_,hcomm,_,hRP,_⟩ :=
    D.sourceOrbit_m22_code_selected_cubic_data h hmany hV hnon d hH s
  exact D.sourceOrbit_m22_code_selected_exclusion h hmany hV hnon d hH s
    hA hAT hfix hker hcent hfour hfive hcomm hRP hTVA

/-- Source 8.2.13 excludes the original M22 code marking. -/
theorem sourceOrbit_m22_code_excluded_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation
      D.orbitComponent m22OuterCodeRepresentation) := by
  rintro ⟨d⟩
  let F := D.fundamentalSetup h.toHypothesis1221
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hu := F.lemma_3_2_3_uniqueness h127
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany F.maximalLocal hu.1
      ((show (T : Subgroup G) ≤ Chapter3.Section02.localJoin T L from le_sup_right).trans hu.2.1))
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,D.localOrbit_eq] using hH
  obtain ⟨I,i,S,s,_⟩ := D.sourceOrbit_m22_code_cubic_pair h hmany hV hnon d hH'
  exact D.sourceOrbit_m22_code_selected_impossible h hmany hV hnon d hH' s

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
