module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSymmetricSeven
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalNormalizationSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Nonsolvable
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# The original paired outside case

The contrary core-free Borel join constructs its literal paired point
amalgam. Its actual point span supplies the bounded B.5 branch, and the
proved F.6 comparisons and point-motion exclusions eliminate every row.
Thus the Borel join has nontrivial two-core, without a terminal-model or
point-exclusion premise. The earlier normalization and Baumann bounds are
supplied by the same original Context and its multiple-overgroup guard.

For an actual wreath quotient, the resulting three-group residual quotient
contradicts the proved original Borel quotient exclusion. No universal
module classification or quotient-action lifting premise is used.

Source: Aschbacher--Smith 13.2.12--14, printed pp.881--884.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- Original 13.2.12 for the actual moving solvable outside subgroup.
All point-amalgam and module alternatives are constructed internally. -/
theorem original_borel_join_core_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) : (H ⊔ borelResidual T L).pCoreIn 2 ≠ ⊥ := by
  intro hcore
  have hn := fun K hK =>
    (Section06.CentralizerReduction.SourceAssembly.original_faithful_normalization_from_source
      d hmany K hK).1
  have hB := baumann_normalizer_of_many d hmany
  have hz := center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore
  have hb := coreFree_borel_join_local_nonblock d hn hH hB hZ hs hcore
  obtain ⟨P₁,horiginal,hPH,hPG,hBP,hout,hinter,hJv,hSyl,hSQ,hg⟩ :=
    coreFree_borel_join_point_goldschmidt_triple d hH hB hZ hs hcore
  let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
  let J := P₁ ⊔ P₂
  have hBJ : ChapterB.baumann (T : Subgroup G) ≤ J := hBP.trans le_sup_left
  have hLJ : Lv L (markedV d.flag.flag.module) ≤ J := le_sup_left.trans le_sup_right
  have hthree := coreFree_borel_join_point_residual_nonblock d hn hH hB hZ hs hcore horiginal
  obtain ⟨hne,hquot,hi,hqcore,hncyc⟩ :=
    point_quotient_of_nonblock d hH hB hZ hs hz hb hout hinter hg
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  obtain ⟨R,hR,hrows⟩ := FSource.sourceClassification_knownSimple_complete _ _ _ hquot
    { Cover := J, sqtk := hSQ, equiv := MulEquiv.refl _ }
  have hRn : ¬ Nonempty (R ≃* FSource.C 2) := by
    rintro ⟨er⟩
    exact hncyc ⟨(MulEquiv.subgroupCongr hR).trans er⟩
  have ha : markedZ d.flag.flag.module * markedV d.flag.flag.module ∈ J.pCoreIn 2 := by
    by_contra ha
    exact hthree (point_residual_block_of_complement_not_mem_core
      d hH hB hZ hs hz horiginal hPH hBP hJv hinter hSQ hg hquot hi ha)
  obtain ⟨x,hx,hr,hff⟩ := point_overgroup_ff_span_of_complement_mem_core
    d hH hB hZ hs hz hBJ hLJ hJv ha
  let := hr.normal
  let := hr.elementary
  let U := conjugateSpanBy (zpowers x) ⊤
  let ρ := ChapterB.InternalThompsonAction.action U
  have hdata := point_span_action_comparison d hH hB hZ hs hz horiginal hPG hinter hg x hx
    U hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  have hrank : primeRank 3 J ≤ 2 := hSQ.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hnotrow := point_not_solvable_F6_row d hH hB hZ hs hz horiginal hPG hinter hg hne
    hrank x hx hr hff
  have hnq : ¬ Group.IsSolvable (J ⧸ pPrimeCore 3 J) :=
    hrows.elim (fun r => FSource.source_alternative_nonsolvable r hRn hnotrow)
      (fun r => FSource.source_alternative_nonsolvable r hRn hnotrow)
  have hnJ : ¬ Group.IsSolvable J := by
    intro hsol
    let := hsol
    exact hnq (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _))
  have hnaction : ¬ Group.IsSolvable (J ⧸ centralizer (U : Set J)) := by
    intro hsol
    exact hnJ ((Group.isSolvable_iff_subgroup_quotient _).mpr ⟨hdata.1,hsol⟩)
  have hgen := point_action_residual_le_offender d hH hB hZ hs hz horiginal hBP hPG hinter hg
    x hx hr
  obtain ⟨hprime,hle,g,hgs,hgf,hker,hsol⟩ :=
    point_action_prime_comparison d hH hB hZ hs hz horiginal hBP hPG hinter hSQ hg x hx hr hff
  obtain ⟨hD,hE,⟨b⟩⟩ := point_action_quasisimple_source d hH hB hZ hs hz horiginal hBP hPG
    hinter hSQ hg hne ⟨R,hRn,hrows⟩ hnotrow x hx hr hff
  let := hD
  let := hsol
  have hcompare := point_quotient_comparison ρ b hgen.2 hr.quotient_pCore_eq_bot g hgs
  have hsimple := point_simple_comparison hcompare b
  have hdegree := point_degree_three_comparison hcompare b hgs
  have hcubic := point_cubic_comparison hcompare b hgs hqcore
  have horder := hrows.elim
    (fun r => point_action_order hcompare hsimple hdegree hcubic hgs hRn r)
    (fun r => point_action_order hcompare hsimple hdegree hcubic hgs hRn r)
  obtain ⟨hactor,hsections⟩ := point_source_sections b horder hgen.2
  have hnot := point_action_not_small_classical d hH hB hZ hs hz horiginal hPG hinter hg
    x hx hr hnaction b hsections
  have hnotg2 := point_action_not_binaryG2 d hH hB hZ hs hz horiginal hPG hinter hg
    x hx hr hnaction b hsections
  have hcovers := point_cubic_six_faithful hcubic hnot
  have hnotcover := point_action_not_triple_alternating_six d hH hB hZ hs hz horiginal hPG
    hinter hg x hx hr hnaction b hsections
  have hsourceA := point_not_triple_alternating_six_source hcovers.1 hnotcover
  have hno := point_action_no_cubic_symmetric_quotient d hH hB hZ hs hz horiginal hPG
    hinter hg x hx hr hnaction b hsections
  have hsourceS := point_not_triple_symmetric_six_source (fun h => ⟨(hcovers.2 h).choose⟩) hno
  have hseven := hrows.elim
    (fun r => point_action_seven_of_source_exclusions
      hcompare hsimple hdegree hcubic hgs hRn r hnot hnotg2 hsourceA hsourceS)
    (fun r => point_action_seven_of_source_exclusions
      hcompare hsimple hdegree hcubic hgs hRn r hnot hnotg2 hsourceA hsourceS)
  exact hseven.elim
    (point_action_not_alternatingSeven d hH hB hZ hs hz hBJ hLJ hJv x hx hr hff b)
    (point_action_not_symmetricSeven d hH hB hZ hs hz hBJ hLJ hJv x hx hr hff b)

/-- The paired wreath row of original 13.2.7, with no join-core,
normalization or point-exclusion premise. -/
theorem paired_outside_centralizes_omega
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H)
    (hpair : Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor)) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  have hn := fun K hK =>
    (Section06.CentralizerReduction.SourceAssembly.original_faithful_normalization_from_source
      d hmany K hK).1
  have hB := baumann_normalizer_of_many d hmany
  exact not_three_borel_quotient d hH hB hZ hs
    (paired_borel_join_residual_mod_primeToThreeCore_isThree d hn hH hB hZ hs hpair
      (original_borel_join_core_ne_bot d hmany hH hZ hs))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
