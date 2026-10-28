module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Extensions
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.OddLinear

/-!
# Maximality of the alternating-seven row

Inspection of the genuine A.3.12 embedding alternatives shows that an A₇
subgroup admits only the equality row. Order comparisons rule out the
smaller simple models, while simplicity rules out the extension rows; the
last two rows retain their actual odd-core quotient maps. No assumption on
the containing group is added.
Source: Aschbacher–Smith A.3.12 and C.5.12–13, printed pp.162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The literal A.3.12 classification admits no proper containing row when
the original smaller subgroup is A₇. No hypothesis on the larger model is
added to the original embedding. -/
theorem eq_of_embedding (B D : Subgroup G) (hBD : B ≤ D)
    (hB : IsAlternating B 7) (hrows : A312Embedding B D) : B = D := by
  have hp := primeCore_eq_bot hB 2
  let e : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot
  have hm : IsAlternating (B ⧸ pCore 2 B) 7 := ⟨e.trans hB.some⟩
  cases hrows with
  | one he => exact he
  | two n hn hs _ _ => exact (not_binary hm (by omega) hs).elim
  | three m hml hs _ _ => exact (not_suzuki hm m (by omega) hs).elim
  | four hs _ _ => exact (not_linear_three_two hm hs).elim
  | five hs _ _ => exact (not_linear_four_two hm hs).elim
  | six hs _ =>
      rcases hs with hs | hs
      · exact (not_alternating_five hB hs).elim
      · exact (not_linear_three_two hB hs).elim
  | seven hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (not_alternating_six hB hs).elim
      · exact (not_alternating_cover_six hB hs).elim
  | eight hs =>
      rcases hs with ⟨p,hp,ho,_,hs,_⟩ | ⟨_,_,hs,_⟩
      · exact (not_odd_linear_two hB hp ho hs).elim
      · exact (not_alternating_five hB hs).elim
  | nine hs =>
      rcases hs with ⟨_,_,_,ho,_,hs,_⟩ | ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (not_odd_special_linear hB ho hs).elim
      · exact (not_alternating_six hB hs).elim
      · exact (not_alternating_cover_six hB hs).elim
  | ten _ hp _ _ hs _ => exact (no_elementary_extension hB hp.one_lt (by decide : 0<2) _ hs).elim
  | eleven hs _ => exact (not_alternating_six hB hs).elim
  | twelve hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩ <;> exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
  | thirteen _ hs =>
      rcases hs with hs | hs | hs | hs
      · exact (not_mathieu_twenty_two hB hs).elim
      · exact (not_linear_three_four hB hs).elim
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<3) _ hs).elim
  | fourteen _ hs =>
      rcases hs with hs | hs | hs
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<6) _ hs).elim
      · exact (no_extraspecial_extension hB _ hs).elim
  | fifteen hs _ => exact (not_alternating_five hB hs).elim
  | sixteen hs _ => exact (no_extraspecial_extension hB _ hs).elim
  | seventeen _ hs =>
      rcases hs with hs | hs | hs | hs | hs | hs
      · exact (no_extraspecial_extension hB _ hs).elim
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<11) _ hs).elim
      · exact (not_alternating_five hm hs).elim
      · exact (not_alternating_cover_six hm hs).elim
      · exact (not_linear_four_two hm hs).elim
      · exact (not_linear_three_two hm hs).elim
  | eighteen _ hs =>
      rcases hs with hs | hs
      · exact (no_cyclic_extraspecial_extension hB 2 _ hs).elim
      · exact (no_homocyclic_four_extension hB _ hs).elim
  | nineteen _ hs =>
      rcases hs with hs | hs
      · exact (no_extraspecial_extension hB _ hs).elim
      · exact (no_elementary_extension hB (by decide : 1<2) (by decide : 0<6) _ hs).elim
  | twenty _ _ hk => rw [hp,card_bot] at hk; norm_num at hk
  | twenty_one _ _ ho _ hg hl => exact (not_odd_core_SL_supplement B D hBD hB hg ho hl).elim
  | twenty_two _ _ _ _ hi => exact (not_odd_core_SL_image B D hBD hB (by decide : Odd 5) hi).elim
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
