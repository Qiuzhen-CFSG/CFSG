module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Rewriting

/-!
# Relator replacements for involutory generators

The recursive M₁ presentations have square-one generators. Adjacent equal
letters can therefore be cancelled, and reversed positive words evaluate to
inverses. These lemmas check the positive-word rewrite traces generated from
the literal relators in `../source/levels.json`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
open Subgroup.CosetWordCertificate

def positive {α : Type*} (w : List α) : Word α := w.map (fun a => (a, true))

def positiveReduce {α : Type*} [DecidableEq α] : List α → List α
  | [] => []
  | a :: w => match positiveReduce w with
    | [] => [a]
    | b :: v => if b = a then v else a :: b :: v

theorem eval_positive_cons {α G : Type*} [Group G] (g : α → G) (a : α) (w : List α) :
    eval g (positive (a :: w)) = g a * eval g (positive w) := by
  simp [positive, eval_cons]

theorem eval_positive_append {α G : Type*} [Group G] (g : α → G) (u v : List α) :
    eval g (positive (u ++ v)) = eval g (positive u) * eval g (positive v) := by
  simp [positive, eval_append]

theorem eval_positive_reduce {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (hg : ∀ a, g a * g a = 1) (w : List α) :
    eval g (positive (positiveReduce w)) = eval g (positive w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [positiveReduce, eval_positive_cons, ← ih]
    cases h : positiveReduce w with
    | nil => simp [positive]
    | cons b v =>
      simp only
      split
      · rename_i hb
        subst b
        simp [eval_positive_cons, ← mul_assoc, hg]
      · simp only [eval_positive_cons]

theorem eval_positive_reverse {α G : Type*} [Group G]
    (g : α → G) (hg : ∀ a, g a * g a = 1) (w : List α) :
    eval g (positive w.reverse) = (eval g (positive w))⁻¹ := by
  induction w with
  | nil => simp [positive]
  | cons a w ih =>
    rw [List.reverse_cons, eval_positive_append, ih]
    simp only [positive, List.map_cons, List.map_nil, eval_cons, eval_nil, ite_true,
      mul_one, mul_inv_rev]
    rw [inv_eq_of_mul_eq_one_left (hg a)]

theorem positive_rewrite_step {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (hg : ∀ a, g a * g a = 1)
    (r pre lhs rhs suffix before after : List α) (negative : Bool) (offset : Nat)
    (hr : eval g (positive r) = 1)
    (hrel : (if negative then r.reverse else r).rotate offset = lhs ++ rhs.reverse)
    (hb : positiveReduce (pre ++ lhs ++ suffix) = before)
    (ha : positiveReduce (pre ++ rhs ++ suffix) = after) :
    eval g (positive before) = eval g (positive after) := by
  have hi : eval g (positive (if negative then r.reverse else r)) = 1 := by
    cases negative <;> simp [eval_positive_reverse, hg, hr]
  have he := eval_rotate g _ hi offset
  dsimp only [positive] at he
  rw [← List.map_rotate] at he
  change eval g (positive ((if negative then r.reverse else r).rotate offset)) = 1 at he
  rw [hrel, eval_positive_append, eval_positive_reverse g hg, mul_inv_eq_one] at he
  rw [← hb, ← ha, eval_positive_reduce g hg, eval_positive_reduce g hg,
    eval_positive_append, eval_positive_append, eval_positive_append, eval_positive_append, he]
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
