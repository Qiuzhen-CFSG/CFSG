module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.Data
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Word substitutions and relator replacements

Adapted from the Janko4 stabilizer-bound development in this repository.
These elementary identities validate the short rewrite certificates in
`Relations`. A replacement is a cyclic conjugate of a defining relator or
its inverse, inserted in a context and followed by free reduction. Word
substitution interprets the child generators in the parent presentation.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
open Subgroup.CosetWordCertificate

def substitute {α β : Type*} (f : β → Word α) (w : Word β) : Word α :=
  w.flatMap (fun a => if a.2 then f a.1 else FreeGroup.invRev (f a.1))

theorem eval_substitute {α β G : Type*} [Group G]
    (g : α → G) (f : β → Word α) (w : Word β) :
    eval g (substitute f w) = eval (fun b => eval g (f b)) w := by
  induction w with
  | nil => simp [substitute]
  | cons a w ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_cons] at *
    rw [ih]
    cases a with
    | mk a sign => cases sign <;> simp [eval_invRev]

theorem eval_rotate {α G : Type*} [Group G] (g : α → G)
    (r : Word α) (hr : eval g r = 1) (offset : Nat) :
    eval g (r.rotate offset) = 1 := by
  simp only [eval, FreeGroup.lift_mk] at *
  simpa only [List.map_rotate] using List.prod_rotate_eq_one_of_prod_eq_one hr offset

theorem rewrite_step {α G : Type*} [Group G] [DecidableEq α] (g : α → G)
    (r pre lhs rhs suffix before after : Word α) (negative : Bool) (offset : Nat)
    (hr : eval g r = 1)
    (hrel : (if negative then FreeGroup.invRev r else r).rotate offset =
      lhs ++ FreeGroup.invRev rhs)
    (hb : reduce (pre ++ lhs ++ suffix) = before)
    (ha : reduce (pre ++ rhs ++ suffix) = after) :
    eval g before = eval g after := by
  have hi : eval g (if negative then FreeGroup.invRev r else r) = 1 := by
    cases negative <;> simp [eval_invRev, hr]
  have he := eval_rotate g _ hi offset
  rw [hrel, eval_append, eval_invRev, mul_inv_eq_one] at he
  rw [← hb, ← ha, eval_reduce, eval_reduce, eval_append, eval_append,
    eval_append, eval_append, he]
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
