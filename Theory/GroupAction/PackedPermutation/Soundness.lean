module
public import Theory.GroupAction.PackedPermutation.Layer
public import Mathlib.GroupTheory.Perm.Basic
/-!
# Composing certified packed switches

Every valid mask determines an actual finite involution. A list of packed
switches acts on table fields by the corresponding product of permutations.
Consequently a checked identity-table computation identifies the original
permutation, and a returned identity table proves its relation. This is the
soundness boundary for the two literal Bray relations used in the Fi24
centralizer quotient in Aschbacher--Smith A.2.19; data generation is untrusted.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

structure Stage where
  distance : ℕ
  mask : ℕ

def Stage.selected (s : Stage) (w i : ℕ) : Bool := s.mask.testBit (w*i)

structure Stage.Valid (s : Stage) (w n : ℕ) : Prop where
  uniform : ∀ i j, j<w → s.mask.testBit (w*i+j) = s.selected w i
  disjoint : ∀ i, s.selected w i = true → s.selected w (i+s.distance) = false
  bounded : ∀ i, s.selected w i = true → i+s.distance<n

def Stage.perm {w n : ℕ} (s : Stage) (h : s.Valid w n) : Equiv.Perm (Fin n) :=
  switchPerm s.distance n (s.selected w) h.disjoint h.bounded

def run (w : ℕ) : List Stage → ℕ → ℕ
  | [], x => x
  | s::ss, x => run w ss (layer w s.distance s.mask x)

def permutation (w n : ℕ) : (ss : List Stage) → (∀ s∈ss, s.Valid w n) → Equiv.Perm (Fin n)
  | [], _ => 1
  | s::ss, h => s.perm (h s (by simp)) * permutation w n ss (fun t ht => h t (by simp [ht]))

theorem get_run (w n x : ℕ) (ss : List Stage) (h : ∀ s∈ss, s.Valid w n) (i : Fin n) :
    get w (run w ss x) i = get w x (permutation w n ss h i) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    rw [run, ih]
    exact layer_get w s.distance s.mask x (s.selected w)
      (h s (by simp)).uniform (h s (by simp)).disjoint _

theorem run_append (w x : ℕ) (ss ts : List Stage) :
    run w (ss++ts) x = run w ts (run w ss x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem get_run_identity (w n ramp : ℕ) (ss : List Stage)
    (h : ∀ s∈ss, s.Valid w n) (hr : ∀ i : Fin n, get w ramp i=i.val) (i : Fin n) :
    get w (run w ss ramp) i = (permutation w n ss h i).val := by
  rw [get_run, hr]

theorem permutation_eq_of_run_identity (w n ramp table : ℕ) (ss : List Stage)
    (h : ∀ s∈ss, s.Valid w n) (hr : ∀ i : Fin n, get w ramp i=i.val)
    (p : Equiv.Perm (Fin n)) (hp : ∀ i : Fin n, get w table i=(p i).val)
    (hcheck : run w ss ramp=table) : permutation w n ss h=p := by
  ext i
  rw [← get_run_identity w n ramp ss h hr i, hcheck, hp]

theorem permutation_eq_one_of_run_identity (w n ramp : ℕ) (ss : List Stage)
    (h : ∀ s∈ss, s.Valid w n) (hr : ∀ i : Fin n, get w ramp i=i.val)
    (hcheck : run w ss ramp=ramp) : permutation w n ss h=1 :=
  permutation_eq_of_run_identity w n ramp ramp ss h hr 1 hr hcheck
end Theory.GroupAction.PackedPermutation
