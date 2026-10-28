module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Extensions
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.OddLinear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.JankoFour

/-!
# Binary C.5.12 rows without a faithful full Sylow

The larger source quotient need not have a faithful Sylow action on the
smaller component. The same twenty-two-row sieve works when the actual
J₄ model has been excluded independently. Its caller supplies that exclusion
from the original moved-module displacement bound, and supplies the genuine
rank-two parabolic-residual theorem. No Sylow-faithfulness premise remains.
Source: Aschbacher–Smith A.3.12 and C.5.12, printed pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

theorem select_binary_rows_with_jankoFour_exclusion (B L : Subgroup G)
    [IsQuasisimple B] (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hBL : B ≤ L) (hJ4 : n = 2 → ¬ Nonempty (L ≃* Janko4.Model))
    (hrows : A312Embedding B L)
    (hRankTwo : RankTwoTheoremC L → IsParabolicResidual B L true → B = L) :
    B = L ∨ n = 2 ∧
      (IsAlternating L 7 ∨ IsAlternatingCover L 7 ∨ Nonempty (L ≃* Janko1.Model) ∨
        ClassicalGroup.IsPSL L 2 25 ∨
        ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL L 2 p) := by
  have hp := binary_primeCore_eq_bot hB 2
  let e : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot
  have hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n) := hB.of_mulEquiv e
  have no3 := binary_not_linear_three_two (by omega : 0<n) hB
  have no4 := binary_not_linear_four_two (by omega : 0<n) hB
  have no6 := binary_not_alternating_six (by omega : 0<n) hB
  have no36 := binary_not_alternating_cover_six (by omega : 0<n) hB
  cases hrows with
  | one he => exact .inl he
  | two _ _ _ hl hr => exact .inl (hRankTwo hl hr)
  | three m hml hs _ _ => exact (binary_not_suzuki hm m (by omega) hs).elim
  | four hs _ _ => exact (binary_not_linear_three_two (by omega) hm hs).elim
  | five hs _ _ => exact (binary_not_linear_four_two (by omega) hm hs).elim
  | six hs hl =>
      rcases hs with hs | hs
      · exact .inr ⟨binary_parameter_of_alternating_five (by omega) hB hs,
          hl.elim Or.inl (fun h => .inr (.inl h))⟩
      · exact (no3 hs).elim
  | seven hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (no6 hs).elim
      · exact (no36 hs).elim
  | eight hs =>
      rcases hs with ⟨p,hp,ho,hgt,hs,hl⟩ | ⟨p,hp,hs,hl⟩
      · obtain ⟨hn2,hp5⟩ := binary_odd_prime_parameters hn hB hp ho hgt hs
        subst p
        exact .inr ⟨hn2,.inr (.inr (.inr (.inl (by simpa using hl))))⟩
      · exact .inr ⟨binary_parameter_of_alternating_five (by omega) hB hs,
          .inr (.inr (.inr (.inr ⟨p,hp,hl⟩)))⟩
  | nine hs =>
      rcases hs with ⟨p,_,_,ho,_,hs,_⟩ | ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (binary_not_odd_special_linear hB ho hs).elim
      · exact (no6 hs).elim
      · exact (no36 hs).elim
  | ten p hp _ _ hs _ => exact (binary_no_elementary_extension hn hB hp.one_lt (by decide : 0<2) _ hs).elim
  | eleven hs _ => exact (no6 hs).elim
  | twelve hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩ <;> exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
  | thirteen _ hs =>
      rcases hs with hs | hs | hs | hs
      · exact (binary_not_mathieu_twenty_two (by omega) hB hs).elim
      · exact (binary_not_linear_three_four (by omega) hB hs).elim
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<3) _ hs).elim
  | fourteen _ hs =>
      rcases hs with hs | hs | hs
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<4) _ hs).elim
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<6) _ hs).elim
      · exact (binary_no_extraspecial_extension hn hB _ hs).elim
  | fifteen hs hl =>
      exact .inr ⟨binary_parameter_of_alternating_five (by omega) hB hs,
        .inr (.inr (.inl hl))⟩
  | sixteen hs _ => exact (binary_no_extraspecial_extension hn hB _ hs).elim
  | seventeen hl hs =>
      rcases hs with hs | hs | hs | hs | hs | hs
      · exact (binary_no_extraspecial_extension hn hB _ hs).elim
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<11) _ hs).elim
      · have hn2 := binary_parameter_of_alternating_five (by omega) hm hs
        subst n
        exact (hJ4 rfl hl).elim
      · exact (binary_not_alternating_cover_six (by omega) hm hs).elim
      · exact (binary_not_linear_four_two (by omega) hm hs).elim
      · exact (binary_not_linear_three_two (by omega) hm hs).elim
  | eighteen _ hs =>
      rcases hs with hs | hs
      · exact (binary_no_cyclic_extraspecial_extension hn hB 2 _ hs).elim
      · exact (binary_no_homocyclic_four_extension hn hB _ hs).elim
  | nineteen _ hs =>
      rcases hs with hs | hs
      · exact (binary_no_extraspecial_extension hn hB _ hs).elim
      · exact (binary_no_elementary_extension hn hB (by decide : 1<2) (by decide : 0<6) _ hs).elim
  | twenty _ _ hk => rw [hp,card_bot] at hk; norm_num at hk
  | twenty_one _ _ ho _ hg hl =>
      exact (binary_not_odd_core_SL_supplement B L hBL hn hB hg ho hl).elim
  | twenty_two _ _ _ _ hi =>
      exact (binary_not_odd_core_SL_image B L hBL hn hB (by decide : Odd 5) hi).elim
/-- The fixed-parameter compatibility API. -/
theorem select_binary_rows_without_faithfulness (B L : Subgroup G)
    [IsQuasisimple B] (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hBL : B ≤ L) (hJ4 : ¬ Nonempty (L ≃* Janko4.Model))
    (hrows : A312Embedding B L)
    (hRankTwo : RankTwoTheoremC L → IsParabolicResidual B L true → B = L) :
    B = L ∨ n = 2 ∧
      (IsAlternating L 7 ∨ IsAlternatingCover L 7 ∨ Nonempty (L ≃* Janko1.Model) ∨
        ClassicalGroup.IsPSL L 2 25 ∨
        ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL L 2 p) :=
  select_binary_rows_with_jankoFour_exclusion B L hn hB hBL (fun _ => hJ4) hrows hRankTwo
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
