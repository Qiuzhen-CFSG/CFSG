module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointAlternatingSeven
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.SevenNatural
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSplit

/-!
# Excluding the original S₇ point-action quotient

The full B.5 conclusion gives compatible natural coordinates and fixed
codimensions on the literal complementary-point span. Its actual common
point Sylow is Baum(T), and Baumann heredity makes it its own Baumann
subgroup. The natural seven-letter calculation forces its Baumann image
to have order eight, contrary to its order-sixteen Sylow image in S₇.
The source application below is used after every original S,I rechoice;
no quotient map or multiple-overgroup hypothesis is replaced.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1, p.99;
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

/-- The literal full point span cannot have S₇ as its faithful actor.
The fixed summand is retained in both natural-coordinate comparisons. -/
theorem point_action_not_symmetricSeven
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
        ¬ Nonempty (E ≃* Equiv.Perm (Fin 7)) := by
  intro x hx hr
  let := hr.normal
  let := hr.elementary
  intro U E ρ N hff b he
  obtain ⟨e⟩ := he
  let f := QuotientGroup.mk' (centralizer (U : Set J))
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U f
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨a,hcod,s,hsi,hse⟩ := SourceSections.SevenNatural.natural_coordinates ρ hf hff b e
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
  exact ChapterC.RankOne.Alternating.SevenSource.natural_not_baumann_sylow
    U f (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) a S
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) hmove hself hcod s hsi hse
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
