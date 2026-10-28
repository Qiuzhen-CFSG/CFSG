module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LinearDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LocalOrders
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.BinaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Mathieu
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.SmallSporadic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoOne

/-!
# Remaining complementary carriers of the actual escaping component

Apply the rank and proper-Sylow reductions to the full central quotient
catalogue. The three small-sporadic exclusions then leave precisely the
binary-linear rows and seven named sporadic carriers. J₁ is excluded by
the central two-core of its perfect subgroups. This is a
proved reduction of the original configuration, not a common-centralizer
inspection for the surviving rows. The imported rank-one comparison
excludes all these rows for an even original binary field degree, and
restricts every other original rank-one case to degree three or five.
The literal two-local order and large-elementary comparisons now exclude
Held, Rudvalis and M₂₄ from those remaining rank-one cases. The J₄
two-local prime-31 and Sylow-three exponent comparisons exclude both
remaining degrees, completing the complementary rank-one family.
For the original binary-three quotient, the native M₂₂ two-local
seven-divisibility obstruction removes M₂₂ for every module row.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- All complementary carriers still requiring inspection, with actual
isomorphisms and no additional premise on the selected module. -/
theorem remaining_carriers [IsQuasisimple I]
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) ∨
    Nonempty ((I ⧸ center I) ≃* Janko1.Model) := by
  rcases binary_or_sporadic D c (center_quotient_model D c) hr with hb | hs
  · exact .inl hb
  · rcases hs with ⟨name,hne,⟨e⟩⟩ | he
    · cases name with
      | m11 => exact (not_mathieuEleven D c e).elim
      | m12 => exact (not_mathieuTwelve D c e).elim
      | m22 => exact .inr (.inl ⟨.m22,by simp,⟨e⟩⟩)
      | m23 => exact .inr (.inl ⟨.m23,by simp,⟨e⟩⟩)
      | m24 => exact .inr (.inl ⟨.m24,by simp,⟨e⟩⟩)
      | j2 => exact (not_jankoTwo D c e).elim
      | j3 => exact (hne rfl).elim
      | j4 => exact .inr (.inl ⟨.j4,by simp,⟨e⟩⟩)
      | hs => exact .inr (.inl ⟨.hs,by simp,⟨e⟩⟩)
      | he => exact .inr (.inl ⟨.he,by simp,⟨e⟩⟩)
      | ru => exact .inr (.inl ⟨.ru,by simp,⟨e⟩⟩)
    · exact .inr (.inr he)

/-- The actual J₁ comparison removes the final low-Sylow sporadic row,
without imposing the A₅-specific bound of sixteen on the moved module. -/
theorem remaining_binary_or_sporadic [IsQuasisimple I]
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases remaining_carriers D c hr with hb | hrest
  · exact .inl hb
  · rcases hrest with hs | he
    · exact .inr hs
    · exact (not_jankoOne D c he.some).elim

/-- The original binary-three quotient removes M₂₂ from the complementary
catalogue, retaining all module rows and actual model isomorphisms. -/
theorem remaining_of_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases remaining_binary_or_sporadic D c hr with hb | ⟨name,hname,⟨e⟩⟩
  · exact .inl hb
  · rcases hname with rfl | hname
    · exact (not_mathieuTwentyTwo_of_binary_three D c dL e).elim
    · exact .inr ⟨name,hname,⟨e⟩⟩

/-- The complementary rank-one inspection now leaves only the actual J₄
carrier, with the original degree three or five. -/
theorem binary_quotient_janko_four [IsQuasisimple I]
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hr : ¬ ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r) :
    (n = 3 ∨ n = 5) ∧ Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  rcases binary_quotient_sporadic_residual D c hn hL hna
      (remaining_binary_or_sporadic D c hr) with ⟨hn3,name,hname,⟨e⟩⟩ | ⟨hn5,e⟩
  · subst n
    rcases hname with rfl | rfl | rfl | rfl
    · exact (not_mathieuTwentyFour_of_degree_three D c hL e).elim
    · exact ⟨.inl rfl,⟨e⟩⟩
    · exact (not_held_of_degree_three D c hL e).elim
    · exact (not_rudvalis_of_degree_three D c hL e).elim
  · exact ⟨.inr hn5,e⟩

/-- Every complementary carrier is excluded for the original non-A₅
binary rank-one quotient. Both remaining J₄ degrees are discharged on
the literal local image, without any assumption on module irreducibility. -/
theorem not_complementary_of_binary_quotient [IsQuasisimple I]
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hr : ¬ ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r) : False := by
  obtain ⟨hdegree,⟨e⟩⟩ := binary_quotient_janko_four D c hn hL hna hr
  rcases hdegree with rfl | rfl
  · exact not_jankoFour_of_degree_three D c hL e
  · exact not_jankoFour_of_degree_five D c hL e

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
