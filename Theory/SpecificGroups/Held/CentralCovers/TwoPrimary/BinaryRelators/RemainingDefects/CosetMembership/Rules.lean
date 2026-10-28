module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership.Words
import Mathlib.Tactic.FinCases

/-!+# A word-action calculus for the centralizer certificate

A system consists of four mutually inverse transitions, the seven literal
relator loops at every point, and the nine seed loops at its origin. Every
certificate fact is an equality of actual points. In the application these
points are right cosets of `centralizerSpan`, not an independently supplied
permutation table. Reversal, composition and prefix cancellation justify all
scans and all unions in the discovery trace.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership

def walk {C : Type*} (step : C → Fin 4 → C) : C → Word → C
  | a, [] => a
  | a, c :: w => walk step (step a c) w

theorem walk_append {C : Type*} (step : C → Fin 4 → C) (a : C) (u v : Word) :
    walk step a (u ++ v) = walk step (walk step a u) v := by
  induction u generalizing a with
  | nil => rfl
  | cons c u ih => exact ih (step a c)

structure System (C : Type*) where
  step : C → Fin 4 → C
  undo : ∀ a c, step (step a c) (flip c) = a
  origin : C
  relators : ∀ (r : Fin 7) a, walk step a (relator r) = a
  seeds : ∀ r : Fin 9, walk step origin (seed r) = origin

theorem walk_inverse {C : Type*} (s : System C) (a : C) (w : Word) :
    walk s.step (walk s.step a w) (inverse w) = a := by
  induction w generalizing a with
  | nil => rfl
  | cons c w ih =>
    simp only [walk, inverse, List.map_cons, List.reverse_cons]
    rw [walk_append]
    change walk s.step (walk s.step (walk s.step (s.step a c) w) (inverse w))
      [flip c] = a
    rw [ih]
    exact s.undo a c

theorem walk_injective {C : Type*} (s : System C) (w : Word) :
    Function.Injective (fun a => walk s.step a w) := by
  intro a b h
  have := congrArg (fun c => walk s.step c (inverse w)) h
  simpa only [walk_inverse] using this

theorem reverse {C : Type*} (s : System C) {a b : C} {w : Word}
    (h : walk s.step a w = b) : walk s.step b (inverse w) = a := by
  rw [← h, walk_inverse]

theorem trans {C : Type*} (s : System C) {a b c : C} {u v : Word}
    (h : walk s.step a u = b) (k : walk s.step b v = c) :
    walk s.step a (u ++ v) = c := by
  rw [walk_append, h, k]

theorem cancel {C : Type*} (s : System C) {a b c : C} {u : Word} (v : Word)
    (h : walk s.step a u = b) (k : walk s.step a (u ++ v) = c) :
    walk s.step b v = c := by
  rw [walk_append, h] at k
  exact k

theorem rotate_loop {C : Type*} (s : System C) (r : Fin 7) (n : Nat) (a : C) :
    walk s.step a ((relator r).rotate n) = a := by
  let u := (relator r).take (n % (relator r).length)
  let v := (relator r).drop (n % (relator r).length)
  have huv : u ++ v = relator r := List.take_append_drop _ _
  have h := s.relators r (walk s.step a v)
  rw [← huv, walk_append] at h
  have k := walk_injective s v h
  simpa only [List.rotate_eq_drop_append_take_mod, walk_append] using k

end Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership
