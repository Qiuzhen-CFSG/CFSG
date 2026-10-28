module

public import Theory.GroupTheory.CosetWordCertificate

/-!
# Sound word operations for elementary Tietze elimination

An established generator equality permits substitution in any signed word.
A finite replay preserves evaluation, and free reduction, inversion and
conjugation preserve relations. These structural lemmas justify the compact
Schreier presentation certificates without a computation oracle.

This is the elementary generator-elimination argument: a relation containing a
single occurrence of a generator solves for that generator in the others.
-/

@[expose] public section
namespace Subgroup.CosetWordCertificate
variable {G α β : Type*} [Group G] [DecidableEq α]
/-- Replace both signs of one generator by a word and its inverse. -/
def substitute (x : α) (v : Word α) : Word α → Word α
  | [] => []
  | (y, b) :: w => (if y = x then if b then v else FreeGroup.invRev v
      else [(y, b)]) ++ substitute x v w

theorem eval_substitute (g : α → G) (x : α) (v w : Word α)
    (h : g x = eval g v) : eval g (substitute x v w) = eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨y, b⟩
    simp only [substitute, eval_append, ih, eval_cons]
    by_cases hy : y = x
    · subst y
      cases b <;> simp [h, eval_invRev]
    · simp [hy]


/-- Check a replay using explicit intermediate words, so no earlier computation
is repeated when checking a later substitution. -/
def checkReplay (ops : β → α × Word α) (steps : List (β × Word α))
    (w result : Word α) : Bool :=
  match steps with
  | [] => decide (w = result)
  | (i, v) :: rest => decide (reduce (substitute (ops i).1 (ops i).2 w) = v) &&
      checkReplay ops rest v result

/-- Checked snapshots and established generator equalities justify the replay. -/
theorem eval_of_checkReplay (g : α → G) (ops : β → α × Word α)
    (steps : List (β × Word α)) (w result : Word α)
    (h : ∀ s ∈ steps, g (ops s.1).1 = eval g (ops s.1).2)
    (hc : checkReplay ops steps w result = true) : eval g result = eval g w := by
  induction steps generalizing w with
  | nil =>
    simp only [checkReplay, decide_eq_true_eq] at hc
    rw [hc]
  | cons s rest ih =>
    rcases s with ⟨i, v⟩
    simp only [checkReplay, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hv : eval g v = eval g w := by
      rw [← hc.1, eval_reduce]
      exact eval_substitute g (ops i).1 (ops i).2 w (h _ (List.mem_cons_self ..))
    exact (ih _ (fun z hz => h z (List.mem_cons_of_mem _ hz)) hc.2).trans hv

/-- A freely checked conjugate (or inverse conjugate) of a relation is a relation. -/
theorem eval_conjugate_checked (g : α → G) (w v p : Word α) (b : Bool)
    (hcheck : reduce (p ++ (if b then w else FreeGroup.invRev w) ++
      FreeGroup.invRev p) = v) (h : eval g w = 1) : eval g v = 1 := by
  rw [← hcheck, eval_reduce, eval_append, eval_append, eval_invRev]
  cases b <;> simp [eval_invRev, h]

omit [DecidableEq α] in
theorem eq_of_eval_relation (g : α → G) (x : α) (v : Word α)
    (h : eval g ([(x, true)] ++ FreeGroup.invRev v) = 1) : g x = eval g v := by
  simpa only [eval_append, eval_letter, ↓reduceIte, eval_invRev,
    mul_inv_eq_one] using h

omit [DecidableEq α] in
theorem eval_map_letters (g : β → G) (f : α → β) (w : Word α) :
    eval g (w.map (fun a => (f a.1, a.2))) = eval (g ∘ f) w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, eval_cons, ih, Function.comp_apply]
end Subgroup.CosetWordCertificate
