module
public import Theory.GroupTheory.WordSubgroup

/-!
# Checked rewriting of finite group words

A word certificate specifies applications of proved word equations at explicit
positions. Each rewrite preserves evaluation in any group. Combining a checked
certificate with generator images gives a checked computation of a group
endomorphism on a word. No completeness or termination claim about collection
is needed.
-/

namespace Theory.GroupTheory.WordRewrite

@[expose] public section
variable {n : ℕ}

structure Rule (n : ℕ) where
  lhs : List (Fin n)
  rhs : List (Fin n)

def rewrite (r : Rule n) : ℕ → List (Fin n) → List (Fin n)
  | 0, w => if w.take r.lhs.length = r.lhs then r.rhs ++ w.drop r.lhs.length else w
  | _+1, [] => []
  | k+1, a::w => a :: rewrite r k w

def execute {ι : Type*} (rules : ι → Rule n) :
    List (ι × ℕ) → List (Fin n) → List (Fin n)
  | [], w => w
  | (r,k)::steps, w => execute rules steps (rewrite (rules r) k w)

variable {G : Type*} [Group G] (x : Fin n → G)

theorem rewrite_sound (r : Rule n) (hr : evalWord x r.lhs = evalWord x r.rhs)
    (k : ℕ) (w : List (Fin n)) : evalWord x (rewrite r k w) = evalWord x w := by
  induction k generalizing w with
  | zero =>
      simp only [rewrite]
      split
      · rename_i h
        have hw : r.lhs ++ w.drop r.lhs.length = w := by
          exact (congrArg (· ++ w.drop r.lhs.length) h.symm).trans
            (List.take_append_drop r.lhs.length w)
        rw [evalWord_append, ←hr, ←evalWord_append, hw]
      · rfl
  | succ k ih =>
      cases w with
      | nil => rfl
      | cons a w => simpa only [rewrite,evalWord] using congrArg (x a * ·) (ih w)

theorem execute_sound {ι : Type*} (rules : ι → Rule n)
    (hr : ∀ i, evalWord x (rules i).lhs = evalWord x (rules i).rhs)
    (steps : List (ι × ℕ)) (w : List (Fin n)) :
    evalWord x (execute rules steps w) = evalWord x w := by
  induction steps generalizing w with
  | nil => rfl
  | cons s steps ih =>
      exact (ih _).trans (rewrite_sound x _ (hr s.1) s.2 w)

theorem eval_flatMap (f : G →* G) (images : Fin n → List (Fin n))
    (hi : ∀ i, evalWord x (images i) = f (x i)) (w : List (Fin n)) :
    evalWord x (w.flatMap images) = f (evalWord x w) := by
  induction w with
  | nil => simp [evalWord]
  | cons a w ih => simp only [List.flatMap_cons,evalWord_append,hi,ih,evalWord,map_mul]

theorem certified_action {ι : Type*} (rules : ι → Rule n)
    (hr : ∀ i, evalWord x (rules i).lhs = evalWord x (rules i).rhs)
    (f : G →* G) (images : Fin n → List (Fin n))
    (hi : ∀ i, evalWord x (images i) = f (x i))
    (steps : List (ι × ℕ)) (w v : List (Fin n))
    (hc : execute rules steps (w.flatMap images) = v) :
    evalWord x v = f (evalWord x w) := by
  rw [←hc]
  exact (execute_sound x rules hr steps _).trans (eval_flatMap x f images hi w)

end
end Theory.GroupTheory.WordRewrite
