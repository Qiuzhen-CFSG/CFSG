module
public import Theory.GroupAction.PackedPermutation.Soundness
/-!
# Words in certified switching networks

Concatenation multiplies the actual wire permutations, reversing the stages
inverts them because every stage is an involution, and concatenating repeated
copies gives the corresponding group power. These identities justify the
network words used for the two literal Fi24 Bray relations; the masks and
source generators still pass through the separate proved soundness checks.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

theorem Stage.perm_inv {w n : ℕ} (s : Stage) (h : s.Valid w n) :
    (s.perm h)⁻¹=s.perm h := rfl

theorem permutation_append (w n : ℕ) (ss ts : List Stage)
    (h : ∀ s∈ss++ts, s.Valid w n) :
    permutation w n (ss++ts) h =
      permutation w n ss (fun s hs => h s (List.mem_append_left _ hs)) *
      permutation w n ts (fun s hs => h s (List.mem_append_right _ hs)) := by
  induction ss with
  | nil => simp [permutation]
  | cons s ss ih =>
    simpa only [List.cons_append, permutation, mul_assoc] using
      congrArg (fun p => s.perm (h s (by simp)) * p) (ih (fun t ht => h t (by simp [ht])))

theorem permutation_reverse (w n : ℕ) (ss : List Stage)
    (h : ∀ s∈ss, s.Valid w n) :
    permutation w n ss.reverse (fun s hs => h s (List.mem_reverse.mp hs)) =
      (permutation w n ss h)⁻¹ := by
  induction ss with
  | nil => simp [permutation]
  | cons s ss ih =>
    simp only [List.reverse_cons, permutation_append]
    simpa only [permutation, mul_one, mul_inv_rev, Stage.perm_inv] using
      congrArg (fun p => p * s.perm (h s (by simp)))
        (ih (fun t ht => h t (by simp [ht])))

theorem permutation_replicate_flatten (w n : ℕ) (ss : List Stage)
    (h : ∀ s∈ss, s.Valid w n) (m : ℕ) :
    permutation w n (List.replicate m ss).flatten
      (fun s hs => by
        obtain ⟨t,ht,hs⟩ := List.mem_flatten.mp hs
        exact h s ((List.mem_replicate.mp ht).2 ▸ hs)) =
      (permutation w n ss h)^m := by
  induction m with
  | zero => simp [permutation]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, permutation_append]
    simpa only [pow_succ'] using congrArg (fun p => permutation w n ss h * p) ih
end Theory.GroupAction.PackedPermutation
