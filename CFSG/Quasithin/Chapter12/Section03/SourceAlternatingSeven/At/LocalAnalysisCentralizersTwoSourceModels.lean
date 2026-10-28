module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceModels
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceModule

/-!
# LocalAnalysisCentralizersTwoSourceModels at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceModels`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

open ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem five_maximal_hypothesis_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hBY : P.five ≤ Y)
    (hq : IsQuasisimple (Y ⧸ pCore 2 Y)) :
    Hypothesis1223 KnownSimple.IsKnownSimple T Y :=
  ⟨⟨S.hypothesis.simpleQTKE,P.five_overgroup_faithful_at structural escape hY hBY,hq⟩,
    S.hypothesis.no_rankTwo,S.hypothesis.no_M22,S.hypothesis.no_M23,S.hypothesis.no_J4⟩

private theorem five_sylow_restriction_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {Y : Subgroup G} (hBY : P.five ≤ Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    ∃ U : Sylow 2 Y, (U : Subgroup Y) = (T : Subgroup G).subgroupOf Y ∧
      P.five.subgroupOf Y ∈ localCComponents U := by
  obtain ⟨U,hU⟩ := (T.subtype (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) (sup_le Y.le_normalizer hTY)
  have hU' : (U : Subgroup Y) = (T : Subgroup G).subgroupOf Y := by
    apply map_injective Y.subtype_injective
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype] using hU
  refine ⟨U,hU',?_⟩
  rw [hU']
  exact local_restrict (P.five_local_family_at structural).1 hBY

private def five_restricted_quotient_at {Y : Subgroup G} (hBY : P.five ≤ Y) :
    (P.five.subgroupOf Y ⧸ pCore 2 (P.five.subgroupOf Y)) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBY) (pCore_map_iso 2 _)).trans P.fiveCoreEquiv

private theorem five_no_solvable_sylow_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {Y : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hBY : P.five < Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    ¬ SolvableSylowOvergroups Y := by
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.1
  obtain ⟨U,hU,_⟩ := P.five_sylow_restriction_at structural hBY.le hTY
  have hUB : (U : Subgroup Y) ≤ normalizer (P.five.subgroupOf Y : Set Y) := by
    rw [hU]
    exact (comap_mono (pointResidual_normalized S.chosen.sylow_normalizes_component
      P.two_central)).trans (le_normalizer_comap Y.subtype)
  intro hs
  have ht := hs.eq_top_of_sylow_normalizes U (P.five.subgroupOf Y) hUB (by
    intro hb
    let := hb
    exact Chapter1.mem_L_not_isSolvable (P.five_local_family_at structural)
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hBY.le).toMonoidHom)
        (subgroupOfEquivOfLe hBY.le).surjective))
  exact hBY.not_ge (subgroupOf_eq_top.mp ht)

private theorem five_no_binary_linear_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {Y : Subgroup G} (hBY : P.five ≤ Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  obtain ⟨U,_,hB⟩ := P.five_sylow_restriction_at structural hBY hTY
  let q := QuotientGroup.mk' (pCore 2 Y)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := Y)
    infer_instance
  let a := e.trans ((BinaryLinear.OuterCyclic.slEquivLinear n).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n)).symm)
  exact FiveLocalFF.BinaryLinear.not_section_binary_linear
    (U.mapSurjective (QuotientGroup.mk'_surjective _)) _
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB q)
    (FiveLocalFF.SolvableQuotients.section_map q _ hB (P.five_restricted_quotient_at hBY)).some
    hn ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨a⟩⟩

private def faithful_central_marking_at
    {Y W : Subgroup G} (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (D : ChosenModule T Y W) {n : ℕ} (hn : 4 ≤ n)
    (e : letI := D.actionCentralizer_normal;
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin n)) :
    CentralQuotient Y ≃* alternatingGroup (Fin n) := by
  let := D.actionCentralizer_normal
  let := hY.quasisimple
  let : Nontrivial (alternatingGroup (Fin n)) := alternatingGroup.nontrivial_of_three_le_card (by simpa using (show 3 ≤ n by omega))
  let r := e.toMonoidHom.comp D.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp D.coreToFaithful_surjective
  exact (centralPreimageQuotientEquiv (pCore 2 Y)).trans
    ((IsQuasisimple.centralQuotientEquiv r hr).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simpa using hn))).trans
        QuotientGroup.quotientBot))

private theorem five_no_eight_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {Y : Subgroup G} (hBY : P.five ≤ Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (e : CentralQuotient Y ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨U,_,hB⟩ := P.five_sylow_restriction_at structural hBY hTY
  let q := QuotientGroup.mk' (centralPreimage (pCore 2 Y))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact centralPreimage_pCore_isSolvable 2
  exact FiveLocalFF.AlternatingSmall.not_section_eight
    (U.mapSurjective (QuotientGroup.mk'_surjective _)) _
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB q)
    (FiveLocalFF.SolvableQuotients.section_map q _ hB (P.five_restricted_quotient_at hBY)).some e

private theorem solvable_sylow_of_central_model_at
    {Y : Subgroup G} {A : Type*} [Group A]
    (hY : Y ∈ Chapter1.L G (T : Subgroup G))
    (e : CentralQuotient Y ≃* A) (ha : SolvableSylowOvergroups A) :
    SolvableSylowOvergroups Y := by
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY
  apply SolvableSylowOvergroups.of_two_kernel
    (QuotientGroup.mk' (pCore 2 Y)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  apply SolvableSylowOvergroups.of_central_quotient
    (QuotientGroup.mk' (center (Y ⧸ pCore 2 Y))) (QuotientGroup.mk'_surjective _) (by simp)
  exact SolvableSylowOvergroups.of_equiv
    ((centralPreimageQuotientEquiv (pCore 2 Y)).symm.trans e) ha

theorem five_quasisimple_maximal_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hBY : P.five < Y)
    (hq : IsQuasisimple (Y ⧸ pCore 2 Y)) :
    ∃ W : Subgroup G, Nonempty (Setup T Y W) := by
  have h := P.five_maximal_hypothesis_at structural escape hY hBY.le hq
  obtain ⟨W,⟨D⟩⟩ := (structural Y h).2.1
  have hTY := D.sylow_normalizes_component
  have hn := P.five_no_solvable_sylow_at structural hY hBY hTY
  have hlift (ha : SolvableSylowOvergroups (Y ⧸ pCore 2 Y)) : False :=
    hn (SolvableSylowOvergroups.of_two_kernel (QuotientGroup.mk' (pCore 2 Y))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) ha)
  have hthree (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : False :=
    hlift (SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simp)))
  let := D.actionCentralizer_normal
  cases modules Y W h D with
  | linear n degree action =>
    rcases degree with rfl | hd
    · exact (hthree action.groupEquiv).elim
    · exact (P.five_no_binary_linear_at structural hBY.le hTY hd action.groupEquiv).elim
  | linearThreeExtension e _ _ => exact (hthree e).elim
  | linearFiveExterior e _ _ =>
    exact (P.five_no_binary_linear_at structural hBY.le hTY (Or.inr rfl) e).elim
  | alternating n lower upper action =>
    let e := faithful_central_marking_at h D (by omega : 4 ≤ n) action.groupEquiv
    have hc : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact (hn (solvable_sylow_of_central_model_at hY.1 e
        (fun _ B _ hb => alternatingGroup.isSolvable_subgroup_five_of_ne_top B hb))).elim
    · exact (hn (solvable_sylow_of_central_model_at hY.1 e
        AlternatingSix.ProperSylowOvergroups.isSolvable)).elim
    · exact ⟨W,⟨⟨h,D,e⟩⟩⟩
    · exact (P.five_no_eight_at structural hBY.le hTY e).elim
  | alternatingSevenFour e _ =>
    exact ⟨W,⟨⟨h,D,faithful_central_marking_at h D (by decide) e⟩⟩⟩
  | g2 action => exact (hlift (SolvableSylowOvergroups.of_equiv action.groupEquiv
      Atlas.G2.binaryDerived_solvableSylowOvergroups)).elim
  | tripleSix e _ _ _ =>
    apply False.elim
    apply hlift
    apply SolvableSylowOvergroups.of_equiv e
    let : Group.IsPerfect Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isPerfect
    apply SolvableSylowOvergroups.of_central_quotient
      (QuotientGroup.mk' (center Atlas.Codes.HexEvenAutomorphisms))
      (QuotientGroup.mk'_surjective _) (by simp)
    exact SolvableSylowOvergroups.of_equiv Representation.Hexacode.even_quotient_center_equiv
      AlternatingSix.ProperSylowOvergroups.isSolvable

theorem two_source_normalizes_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    centralizer ({(P.two : G)} : Set G) ≤ normalizer (P.five : Set G) :=
  P.two_normalizes_of_quasisimple_maximal_models_at structural escape natural
    (fun _ hY hBY hq => P.five_quasisimple_maximal_models_at structural modules escape hY hBY hq)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace PointCentralizers

def localAnalysis_of_omegaSpan_at
    (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (hm : ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆) : S.LocalAnalysis := by
  have hK := P.two_source_normalizes_at structural modules escape natural
  exact localAnalysis_of_twoInput_at P structural
    ⟨hK,P.two_section_fixes_moved_of_normalizes_at structural
      ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
        (P.two_moved_normalized_of_omegaSpan_commutator hK hm))⟩

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

