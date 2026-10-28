module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation

/-!
# A replay calculus for lifted G₂(3) word identities

Split cyclic variants of the original relators into word equalities, resolve
critical overlaps, and replay contextual substitutions. All executable checks
compare explicit words; their group interpretation follows from these structural
proofs. The order-nine certificate is a concrete consumer.

Source: the six ATLAS G23G1-P1 relators fixed by `PresentationBound.Subgroup`.
The certificate producers are untrusted.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.Replay
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G] (g : Bool → G)

def variant (w : Word Bool) (inverse : Bool) (offset : Nat) : Word Bool :=
  (if inverse then FreeGroup.invRev w else w).rotate offset

theorem eval_rotate_one (w : Word Bool) (offset : Nat) (h : eval g w = 1) :
    eval g (w.rotate offset) = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, eval_append]
  have hh := h
  rw [← List.take_append_drop (offset % w.length) w, eval_append] at hh
  exact mul_eq_one_comm.mp hh

theorem eval_variant_one (w : Word Bool) (inverse : Bool) (offset : Nat)
    (h : eval g w = 1) : eval g (variant w inverse offset) = 1 := by
  apply eval_rotate_one
  cases inverse <;> simp [h, eval_invRev]

theorem split_relation (w u v : Word Bool) (inverse : Bool) (offset : Nat)
    (hc : variant w inverse offset = u ++ FreeGroup.invRev v)
    (h : eval g w = 1) : eval g u = eval g v := by
  have hh := eval_variant_one g w inverse offset h
  rw [hc, eval_append, eval_invRev, mul_inv_eq_one] at hh
  exact hh

theorem context (p q u v : Word Bool) (h : eval g u = eval g v) :
    eval g (p ++ u ++ q) = eval g (p ++ v ++ q) := by
  simp only [eval_append, h]

theorem overlap (p m q u v : Word Bool)
    (h₁ : eval g (p ++ m) = eval g u) (h₂ : eval g (m ++ q) = eval g v) :
    eval g (u ++ q) = eval g (p ++ v) := by
  simp only [eval_append] at *
  rw [← h₁, ← h₂, mul_assoc]

abbrev Database := Nat → Word Bool × Word Bool

def rewriteAt (db : Database) (w : Word Bool) (s : Nat × Nat) : Option (Word Bool) :=
  let u := (db s.1).1
  if (w.drop s.2).take u.length == u then
    some (w.take s.2 ++ (db s.1).2 ++ w.drop (s.2 + u.length))
  else none

theorem rewriteAt_sound (db : Database) (w : Word Bool) (s : Nat × Nat)
    (hs : eval g (db s.1).1 = eval g (db s.1).2) {v : Word Bool}
    (hc : rewriteAt db w s = some v) : eval g w = eval g v := by
  simp only [rewriteAt] at hc
  split at hc
  · rename_i he
    have he' : (w.drop s.2).take (db s.1).1.length = (db s.1).1 := by simpa using he
    cases hc
    have hw : w = w.take s.2 ++ (db s.1).1 ++ w.drop (s.2 + (db s.1).1.length) := by
      conv_lhs => rw [← List.take_append_drop s.2 w]
      conv_lhs => arg 2; rw [← List.take_append_drop (db s.1).1.length (w.drop s.2)]
      simp only [he', List.drop_drop, List.append_assoc]
    conv_lhs => rw [hw]
    exact context g _ _ _ _ hs
  · contradiction

def replay (db : Database) : Word Bool → List (Nat × Nat) → Option (Word Bool)
  | w, [] => some w
  | w, s :: ss => (rewriteAt db w s).bind fun v => replay db v ss

theorem replay_sound (db : Database) (w : Word Bool) (ss : List (Nat × Nat))
    (hs : ∀ s ∈ ss, eval g (db s.1).1 = eval g (db s.1).2) {v : Word Bool}
    (hc : replay db w ss = some v) : eval g w = eval g v := by
  induction ss generalizing w with
  | nil => cases hc; rfl
  | cons s ss ih =>
    simp only [replay, Option.bind_eq_some_iff] at hc
    obtain ⟨u, hu, hv⟩ := hc
    exact (rewriteAt_sound g db w s (hs _ (List.mem_cons_self ..)) hu).trans
      (ih _ (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hv)


def ValidBefore (db : Database) (n : Nat) : Prop :=
  ∀ i, i < n → eval g (db i).1 = eval g (db i).2

theorem valid_zero (db : Database) : ValidBefore g db 0 := by
  intro i hi
  omega

theorem valid_succ (db : Database) (n : Nat) (h : ValidBefore g db n)
    (hn : eval g (db n).1 = eval g (db n).2) : ValidBefore g db (n + 1) := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact hn

theorem replay_prefix (db : Database) (n : Nat) (w v : Word Bool)
    (ss : List (Nat × Nat)) (h : ValidBefore g db n)
    (hb : ss.all (fun s => decide (s.1 < n)) = true)
    (hc : replay db w ss = some v) : eval g w = eval g v := by
  apply replay_sound g db w ss _ hc
  intro s hs
  exact h s.1 (of_decide_eq_true (List.all_eq_true.mp hb s hs))

def expand (f : Bool → Word Bool) (w : Word Bool) : Word Bool :=
  w.flatMap fun a => if a.2 then f a.1 else FreeGroup.invRev (f a.1)

theorem eval_expand (f : Bool → Word Bool) (w : Word Bool) :
    eval g (expand f w) = eval (fun s => eval g (f s)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [expand, List.flatMap_cons, eval_append] at *
    rw [ih, eval_cons]
    cases a with
    | mk a sign => cases sign <;> simp [eval_invRev]

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.Replay
