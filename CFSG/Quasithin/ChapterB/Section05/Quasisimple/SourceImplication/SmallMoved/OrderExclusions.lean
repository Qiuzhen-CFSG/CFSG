module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Catalogue
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
/-!
# Orders excluded by the small-offender catalogue

Counting the actual binary linear, alternating, SL3(4), and Sp4(4)
carriers separates every row from orders 1080 and 6048. This supplies the
intersection with the earlier faithful-local list in the contrary case
of 13.7.16(2); it makes no classification assertion by itself.

Source: Aschbacher--Smith, 13.7.15(1) and 13.7.16(2), pp.943--944.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

theorem ActorList.card_ne_1080_and_6048 {D : Type*} [Group D] (h : ActorList D) :
    Nat.card D ≠ 1080 ∧ Nat.card D ≠ 6048 := by
  rcases h with ⟨n,hn,hu,⟨e⟩⟩ | ⟨n,hn,hu,⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
  · rw [Nat.card_congr (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))).toEquiv,
      binary_card]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  · interval_cases n <;> rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  · obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,
      BinaryField.four.card_eq]
    decide
  · obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,
      BinaryField.four.card_eq]
    decide
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
