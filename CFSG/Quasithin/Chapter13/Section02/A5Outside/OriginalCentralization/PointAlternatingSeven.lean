module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSevenSelection
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.SevenSplitting
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalSplit

/-!
# Excluding the original A₇ point-action quotient

The original complementary-point span is an FF module, and B.5 forces
its A₇ moved space to have dimension four with a fixed complement. The
actual common point Sylow is Baum(T). Baumann heredity makes it its own
Baumann subgroup. The exceptional module theorem, applied to the actual
commutator subgroup of the span, gives a Baumann image of order four,
contradicting the order-eight Sylow image in A₇.

No identification of the full span with its moved central section is
assumed. The universal SourceAssembly/PointAlternatingSeven consumer applies
this exclusion after every original rechoice, preserving both quotient
maps and the multiple-overgroup guard. The S₇ branch remains separate.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1(2), p.99;
B.2.20 and C.1.24, pp.82,131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The actual original point action cannot be A₇. B.5 first supplies the
four-dimensional moved subgroup with fixed complement. Baumann heredity
then contradicts the order of its actual Sylow image. -/
theorem point_action_not_alternatingSeven
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {J : Subgroup G} (hBJ : ChapterB.baumann (T : Subgroup G) ≤ J)
    (hLJ : Lv L (markedV d.flag.flag.module) ≤ J)
    (hJv : J ≤ Gv (markedV d.flag.flag.module)) :
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let U := conjugateSpanBy (zpowers x) ⊤
      let E := J ⧸ centralizer (U : Set J)
      let ρ := ChapterB.InternalThompsonAction.action U
      let N := offenderSubgroup ρ
      IsFFModule ρ →
      ∀ _b : QuasisimpleComparison.BoundedBranch (ρ.comp N.subtype),
        ¬ Nonempty (E ≃* alternatingGroup (Fin 7)) := by
  intro x hx hr
  let := hr.normal
  let := hr.elementary
  intro U E ρ N hff b he
  obtain ⟨e⟩ := he
  obtain ⟨hcompl,hdim⟩ := SourceSections.Seven.offender_moved_split ρ hff b e
  let f := QuotientGroup.mk' (centralizer (U : Set J))
  obtain ⟨S,hS⟩ := (point_baumann_sylow d hH hB hZ hs hz).restrict hBJ hJv
  have hSR : (S : Subgroup J) = (ChapterB.baumann (T : Subgroup G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hBJ]
  have hself : ChapterB.baumann (S : Subgroup J) = (S : Subgroup J) := by
    apply map_injective J.subtype_injective
    have hm := baumann_map_injective J.subtype J.subtype_injective (S : Subgroup J)
    change (ChapterB.baumann (S : Subgroup J)).map J.subtype =
      ChapterB.baumann ((S : Subgroup J).map J.subtype) at hm
    rw [hm,hS]
    exact baumann_eq_of_intermediate (T : Subgroup G)
      (ChapterB.baumann (T : Subgroup G)) le_rfl inf_le_left
  have hmove : ¬ elementaryAbelianMaxJ (S : Subgroup J) ≤ f.ker := by
    rw [hSR,QuotientGroup.ker_mk']
    exact point_span_thompson_moves d hH hB hZ hs hz hBJ hLJ hJv x hx
  exact ChapterC.RankOne.Alternating.SevenSource.exceptional_not_baumann_sylow_of_split
    U f (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) e S
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) hmove hself hcompl hdim
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
