module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceModule
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.GroupTheory.SolvableSylowOvergroupLifts
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel

/-!
# The maximal-overcomponent sieve for the weight-two point

A faithful proper quasisimple maximal overcomponent satisfies the original
12.2.3 hypotheses. Its actual seven-case module list is compared with the
literal A₅ section: solvable Sylow overgroups exclude the small rows, and
solvable-kernel transport excludes SL₄(2), SL₅(2) and A₈. The surviving A₇
marking supplies a second source setup, already excluded by rigidity.
Thus the original A₅ residual is normal in C_G(e(2)).

The LocalAnalysis consumer retains only the B.5 omega-span equality. Its
proof remains with qt-d-1236-1238-point-centralizers before assembly by
qt-d-1231-local-analysis. Source: Aschbacher–Smith, 12.3.8, printed p.810,
using A.3.14 and 12.2.2.
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

theorem five_maximal_hypothesis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hBY : P.five ≤ Y)
    (hq : IsQuasisimple (Y ⧸ pCore 2 Y)) :
    Hypothesis1223 KnownSimple.IsKnownSimple T Y :=
  ⟨⟨S.hypothesis.simpleQTKE,P.five_overgroup_faithful structural escape hY hBY,hq⟩,
    S.hypothesis.no_rankTwo,S.hypothesis.no_M22,S.hypothesis.no_M23,S.hypothesis.no_J4⟩

private theorem five_sylow_restriction
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
  exact local_restrict (P.five_local_family structural).1 hBY

private def five_restricted_quotient {Y : Subgroup G} (hBY : P.five ≤ Y) :
    (P.five.subgroupOf Y ⧸ pCore 2 (P.five.subgroupOf Y)) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBY) (pCore_map_iso 2 _)).trans P.fiveCoreEquiv

private theorem five_no_solvable_sylow
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {Y : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hBY : P.five < Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    ¬ SolvableSylowOvergroups Y := by
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.1
  obtain ⟨U,hU,_⟩ := P.five_sylow_restriction structural hBY.le hTY
  have hUB : (U : Subgroup Y) ≤ normalizer (P.five.subgroupOf Y : Set Y) := by
    rw [hU]
    exact (comap_mono (pointResidual_normalized S.chosen.sylow_normalizes_component
      P.two_central)).trans (le_normalizer_comap Y.subtype)
  intro hs
  have ht := hs.eq_top_of_sylow_normalizes U (P.five.subgroupOf Y) hUB (by
    intro hb
    let := hb
    exact Chapter1.mem_L_not_isSolvable (P.five_local_family structural)
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hBY.le).toMonoidHom)
        (subgroupOfEquivOfLe hBY.le).surjective))
  exact hBY.not_ge (subgroupOf_eq_top.mp ht)

private theorem five_no_binary_linear
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {Y : Subgroup G} (hBY : P.five ≤ Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  obtain ⟨U,_,hB⟩ := P.five_sylow_restriction structural hBY hTY
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
    (FiveLocalFF.SolvableQuotients.section_map q _ hB (P.five_restricted_quotient hBY)).some
    hn ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨a⟩⟩

private def faithful_central_marking
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

private theorem five_no_eight
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {Y : Subgroup G} (hBY : P.five ≤ Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (e : CentralQuotient Y ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨U,_,hB⟩ := P.five_sylow_restriction structural hBY hTY
  let q := QuotientGroup.mk' (centralPreimage (pCore 2 Y))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact centralPreimage_pCore_isSolvable 2
  exact FiveLocalFF.AlternatingSmall.not_section_eight
    (U.mapSurjective (QuotientGroup.mk'_surjective _)) _
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB q)
    (FiveLocalFF.SolvableQuotients.section_map q _ hB (P.five_restricted_quotient hBY)).some e

private theorem solvable_sylow_of_central_model
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

/-- The actual seven-module list leaves only the central A₇ quotient for a
proper quasisimple maximal overcomponent of the original weight-two residual. -/
theorem five_quasisimple_maximal_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hBY : P.five < Y)
    (hq : IsQuasisimple (Y ⧸ pCore 2 Y)) :
    ∃ W : Subgroup G, Nonempty (Setup T Y W) := by
  have h := P.five_maximal_hypothesis structural escape hY hBY.le hq
  obtain ⟨W,⟨D⟩⟩ := (structural G T Y h).2.1
  have hTY := D.sylow_normalizes_component
  have hn := P.five_no_solvable_sylow structural hY hBY hTY
  have hlift (ha : SolvableSylowOvergroups (Y ⧸ pCore 2 Y)) : False :=
    hn (SolvableSylowOvergroups.of_two_kernel (QuotientGroup.mk' (pCore 2 Y))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) ha)
  have hthree (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : False :=
    hlift (SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simp)))
  let := D.actionCentralizer_normal
  cases modules G T Y W h D with
  | linear n degree action =>
    rcases degree with rfl | hd
    · exact (hthree action.groupEquiv).elim
    · exact (P.five_no_binary_linear structural hBY.le hTY hd action.groupEquiv).elim
  | linearThreeExtension e _ _ => exact (hthree e).elim
  | linearFiveExterior e _ _ =>
    exact (P.five_no_binary_linear structural hBY.le hTY (Or.inr rfl) e).elim
  | alternating n lower upper action =>
    let e := faithful_central_marking h D (by omega : 4 ≤ n) action.groupEquiv
    have hc : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · exact (hn (solvable_sylow_of_central_model hY.1 e
        (fun _ B _ hb => alternatingGroup.isSolvable_subgroup_five_of_ne_top B hb))).elim
    · exact (hn (solvable_sylow_of_central_model hY.1 e
        AlternatingSix.ProperSylowOvergroups.isSolvable)).elim
    · exact ⟨W,⟨⟨h,D,e⟩⟩⟩
    · exact (P.five_no_eight structural hBY.le hTY e).elim
  | alternatingSevenFour e _ =>
    exact ⟨W,⟨⟨h,D,faithful_central_marking h D (by decide) e⟩⟩⟩
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

/-- Relative normality in the actual weight-two point centralizer, after
all proper maximal overcomponent branches have been excluded. -/
theorem two_source_normalizes
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates) :
    centralizer ({(P.two : G)} : Set G) ≤ normalizer (P.five : Set G) :=
  P.two_normalizes_of_quasisimple_maximal_models structural escape natural
    (fun _ hY hBY hq => P.five_quasisimple_maximal_models structural modules escape hY hBY hq)

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace PointCentralizers

/-- The literal LocalAnalysis application after every component branch is
closed. Only the original B.5 moved-space equality remains to be proved. -/
def localAnalysis_of_omegaSpan
    (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (hm : ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆) : S.LocalAnalysis := by
  have hK := P.two_source_normalizes structural modules escape natural
  exact localAnalysis_of_twoInput P structural
    ⟨hK,P.two_section_fixes_moved_of_normalizes structural
      ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
        (P.two_moved_normalized_of_omegaSpan_commutator hK hm))⟩

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
