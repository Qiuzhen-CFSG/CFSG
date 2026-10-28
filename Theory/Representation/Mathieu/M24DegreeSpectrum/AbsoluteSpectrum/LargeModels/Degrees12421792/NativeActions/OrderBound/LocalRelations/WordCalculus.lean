module
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Word replay for the lifted M24 subgroup relations

Cyclic splitting, critical overlaps and contextual substitutions preserve
word evaluation in an arbitrary group. These are the soundness rules for
source-derived word certificates, independently of presentation faithfulness.
`ShortWords` connects expansion to the literal ATLAS max8 generators.

Adapted from the repository's G₂(3) `LocalRelations.WordCalculus` (Apache-2.0).
The concrete source words are John Bray's ATLAS M24G1-P1 and M24G1-max8W1;
see `../source/README.md`. No certificate search is a proof until replayed.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Replay
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G] (g : Fin 2 → G)

def variant (w : Word (Fin 2)) (inverse : Bool) (offset : Nat) : Word (Fin 2) :=
  (if inverse then FreeGroup.invRev w else w).rotate offset

theorem eval_rotate_one (w : Word (Fin 2)) (offset : Nat) (h : eval g w = 1) :
    eval g (w.rotate offset) = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, eval_append]
  have hh := h
  rw [← List.take_append_drop (offset % w.length) w, eval_append] at hh
  exact mul_eq_one_comm.mp hh

theorem eval_variant_one (w : Word (Fin 2)) (inverse : Bool) (offset : Nat)
    (h : eval g w = 1) : eval g (variant w inverse offset) = 1 := by
  apply eval_rotate_one
  cases inverse <;> simp [h, eval_invRev]

theorem split_relation (w u v : Word (Fin 2)) (inverse : Bool) (offset : Nat)
    (hc : variant w inverse offset = u ++ FreeGroup.invRev v)
    (h : eval g w = 1) : eval g u = eval g v := by
  have hh := eval_variant_one g w inverse offset h
  rw [hc, eval_append, eval_invRev, mul_inv_eq_one] at hh
  exact hh

theorem context (p q u v : Word (Fin 2)) (h : eval g u = eval g v) :
    eval g (p ++ u ++ q) = eval g (p ++ v ++ q) := by
  simp only [eval_append, h]

theorem overlap (p m q u v : Word (Fin 2))
    (h₁ : eval g (p ++ m) = eval g u) (h₂ : eval g (m ++ q) = eval g v) :
    eval g (u ++ q) = eval g (p ++ v) := by
  simp only [eval_append] at *
  rw [← h₁, ← h₂, mul_assoc]

abbrev Database := Nat → Word (Fin 2) × Word (Fin 2)

def rewriteAt (db : Database) (w : Word (Fin 2)) (s : Nat × Nat) : Option (Word (Fin 2)) :=
  let u := (db s.1).1
  if (w.drop s.2).take u.length == u then
    some (w.take s.2 ++ (db s.1).2 ++ w.drop (s.2 + u.length))
  else none

theorem rewriteAt_sound (db : Database) (w : Word (Fin 2)) (s : Nat × Nat)
    (hs : eval g (db s.1).1 = eval g (db s.1).2) {v : Word (Fin 2)}
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

def replay (db : Database) : Word (Fin 2) → List (Nat × Nat) → Option (Word (Fin 2))
  | w, [] => some w
  | w, s :: ss => (rewriteAt db w s).bind fun v => replay db v ss

theorem replay_sound (db : Database) (w : Word (Fin 2)) (ss : List (Nat × Nat))
    (hs : ∀ s ∈ ss, eval g (db s.1).1 = eval g (db s.1).2) {v : Word (Fin 2)}
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

theorem replay_prefix (db : Database) (n : Nat) (w v : Word (Fin 2))
    (ss : List (Nat × Nat)) (h : ValidBefore g db n)
    (hb : ss.all (fun s => decide (s.1 < n)) = true)
    (hc : replay db w ss = some v) : eval g w = eval g v := by
  apply replay_sound g db w ss _ hc
  intro s hs
  exact h s.1 (of_decide_eq_true (List.all_eq_true.mp hb s hs))

def expand (f : Fin 2 → Word (Fin 2)) (w : Word (Fin 2)) : Word (Fin 2) :=
  w.flatMap fun a => if a.2 then f a.1 else FreeGroup.invRev (f a.1)

theorem eval_expand (f : Fin 2 → Word (Fin 2)) (w : Word (Fin 2)) :
    eval g (expand f w) = eval (fun s => eval g (f s)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [expand, List.flatMap_cons, eval_append] at *
    rw [ih, eval_cons]
    cases a with
    | mk a sign => cases sign <;> simp [eval_invRev]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.LocalRelations.Replay
