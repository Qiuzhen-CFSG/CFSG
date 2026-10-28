module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.Data
public import Mathlib.Data.List.Sort

/-!
# Checking the action of a disjoint cycle partition

A checked rearrangement of the flattened cycle list proves that it partitions
all 4928 points. Local action checks on each short cycle then determine the
product permutation. Singleton cycles may be added for fixed points without
changing the published product. A structural merge routine makes the
rearrangement certificate reducible by the kernel; its permutation property,
rather than any untrusted sorting algorithm, is the mathematical input.

This supports the literal ATLAS data for Aschbacher–Smith I.1.3(4).
-/

@[expose] public section

namespace Sporadic.Mathieu.M22CyclicFour.WordCertificates

private theorem prod_fixes {α : Type*} [DecidableEq α] (cs : List (List α)) (x : α)
    (h : ∀ c ∈ cs, x ∉ c) : (cs.map List.formPerm).prod x = x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    exact List.formPerm_apply_of_notMem (h c List.mem_cons_self)

private theorem prod_apply {α : Type*} [DecidableEq α] (cs : List (List α))
    (hd : cs.Pairwise List.Disjoint) (c : List α) (hc : c ∈ cs) (x : α) (hx : x ∈ c) :
    (cs.map List.formPerm).prod x = List.formPerm c x := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    obtain ⟨hdds, hds⟩ := List.pairwise_cons.mp hd
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [prod_fixes ds x (fun e he hx' => List.disjoint_left.mp (hdds e he) hx hx')]
    · rw [ih hds hc]
      apply List.formPerm_apply_of_notMem
      intro hxd
      exact List.disjoint_left.mp (hdds c hc) hxd (List.formPerm_apply_mem_of_mem hx)

def merge (fuel : Nat) (xs ys : List Nat) : List Nat :=
  match fuel, xs, ys with
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: merge n xs (y :: ys) else y :: merge n (x :: xs) ys

theorem merge_perm (fuel : Nat) (xs ys : List Nat) : (merge fuel xs ys).Perm (xs ++ ys) := by
  induction fuel generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · exact (ih xs (y :: ys)).cons x
        · exact ((ih (x :: xs) ys).cons y).trans (List.perm_middle.symm)

def sort (depth : Nat) (xs : List Nat) : List Nat :=
  match depth with
  | 0 => xs
  | n + 1 => merge xs.length (sort n (xs.take (xs.length / 2)))
      (sort n (xs.drop (xs.length / 2)))

theorem sort_perm (depth : Nat) (xs : List Nat) : (sort depth xs).Perm xs := by
  induction depth generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    exact (merge_perm _ _ _).trans (by
      simpa only [List.take_append_drop] using (ih (xs.take (xs.length / 2))).append
        (ih (xs.drop (xs.length / 2))))

/-- A partition into cycles determines the action of their product by local checks. -/
theorem action_of_partition {α : Type*} [DecidableEq α] (cs : List (List α))
    (hn : cs.flatten.Nodup) (hc : ∀ x : α, x ∈ cs.flatten) (f : α → α)
    (hf : ∀ c ∈ cs, ∀ x ∈ c, List.formPerm c x = f x) :
    ∀ x, (cs.map List.formPerm).prod x = f x := by
  intro x
  obtain ⟨c, hc, hx⟩ := List.mem_flatten.mp (hc x)
  exact (prod_apply cs (List.nodup_flatten.mp hn).2 c hc x hx).trans (hf c hc x hx)

def point (i : Nat) : Fin 4928 := ⟨i % 4928, Nat.mod_lt _ (by decide)⟩

def finCycles (cs : List (List Nat)) : List (List (Fin 4928)) := cs.map (List.map point)

theorem partition_of_sort (cs : List (List Nat))
    (hs : sort 13 cs.flatten = List.range 4928) :
    (finCycles cs).flatten.Nodup ∧ ∀ x : Fin 4928, x ∈ (finCycles cs).flatten := by
  have hp : cs.flatten.Perm (List.range 4928) := by
    rw [← hs]
    exact (sort_perm _ _).symm
  have hp' : (finCycles cs).flatten.Perm ((List.range 4928).map point) := by
    simpa [finCycles, List.map_flatten] using hp.map point
  constructor
  · apply hp'.nodup_iff.mpr
    apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy h
    have he := congrArg Fin.val h
    simpa [point, Nat.mod_eq_of_lt (List.mem_range.mp hx),
      Nat.mod_eq_of_lt (List.mem_range.mp hy)] using he
  · intro x
    apply hp'.mem_iff.mpr
    apply List.mem_map.mpr
    refine ⟨x.val, List.mem_range.mpr x.isLt, ?_⟩
    exact Fin.ext (Nat.mod_eq_of_lt x.isLt)

def cycleCheck (cs : List (List Nat)) (f : Fin 4928 → Fin 4928) : Bool :=
  cs.all fun c => c.all fun i => decide (List.formPerm (c.map point) (point i) = f (point i))

theorem action_of_checks (cs : List (List Nat)) (f : Fin 4928 → Fin 4928)
    (hs : sort 13 cs.flatten = List.range 4928)
    (hf : cycleCheck cs f = true) :
    ∀ x, ((finCycles cs).map List.formPerm).prod x = f x := by
  obtain ⟨hn, hc⟩ := partition_of_sort cs hs
  apply action_of_partition _ hn hc
  intro c hc x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hf d hd) i hi)

theorem ofCycles_append_fixed (cs : List (List Nat)) (fixed : List Nat) :
    ((finCycles (cs ++ fixed.map (fun i => [i]))).map List.formPerm).prod =
      Data.ofCycles cs := by
  simp only [finCycles, List.map_append, List.prod_append, List.map_map, Function.comp_def,
    List.map_singleton, List.formPerm_singleton, List.map_const', List.prod_replicate, one_pow, mul_one]
  rfl

end Sporadic.Mathieu.M22CyclicFour.WordCertificates
