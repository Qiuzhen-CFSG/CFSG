module
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The six-point stabilizer chain from adjacent relations

Five involutions satisfying the adjacent braid and distant commutation
relations have faithful standard six-point action whenever they generate.
The proof constructs the successive point-stabilizer covers with 6, 5, 4,
3 and 2 representatives. The 70 forward transitions use only 80 elementary
word rewrites; involutivity supplies inverse transitions. A kernel element
falls down the entire chain to the trivial subgroup.

This is the elementary symmetric-group presentation argument, specialized
for the native Held kernel certificate. It uses no group-order comparison.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
open Subgroup
variable {G : Type*} [Group G]
@[expose] public def ev (s : Fin 5 → G) (w : List (Fin 5)) : G := (w.map s).prod
@[simp] private theorem ev_nil (s : Fin 5 → G) : ev s [] = 1 := rfl
private theorem ev_append (s : Fin 5 → G) (u v : List (Fin 5)) : ev s (u ++ v) = ev s u * ev s v := by simp [ev]
private theorem replaceWord (s : Fin 5 → G) (p u v q : List (Fin 5)) (h : ev s u = ev s v) :
    ev s (p ++ u ++ q) = ev s (p ++ v ++ q) := by simp only [ev_append, h]
private def repWord (l r : Fin 6) : List (Fin 5) :=
  (List.finRange 5).filter (fun a => l.val ≤ a.val ∧ a.val < r.val)
private def dest (r : Fin 6) (a : Fin 5) : Fin 6 :=
  if r.val = a.val then ⟨a.val + 1, by omega⟩
  else if r.val = a.val + 1 then a.castSucc else r
private def factor (r : Fin 6) (a : Fin 5) : List (Fin 5) :=
  if r.val = a.val ∨ r.val = a.val + 1 then []
  else if h : a.val + 1 < r.val then [⟨a.val + 1, by omega⟩] else [a]

private theorem transitions (s : Fin 5 → G)
    (hs : ∀ a, ev s [a,a] = ev s [])
    (hc : ∀ a b : Fin 5, a.val + 1 < b.val ∨ b.val + 1 < a.val → ev s [a,b] = ev s [b,a])
    (hb : ∀ a b : Fin 5, a.val + 1 = b.val ∨ b.val + 1 = a.val → ev s [a,b,a] = ev s [b,a,b])
    (l r : Fin 6) (a : Fin 5) (hl : l.val < 5) (hr : l ≤ r) (ha : l.val ≤ a.val) :
    ev s (repWord l r ++ [a]) = ev s (factor r a ++ repWord l (dest r a)) := by
  fin_cases l <;> fin_cases r <;> fin_cases a
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change ev s [0, 0] = ev s []
    exact (replaceWord s [] [0, 0] [] [] (hs 0))
  · rfl
  · change ev s [0, 2] = ev s [2, 0]
    exact (replaceWord s [] [0, 2] [2, 0] [] (hc 0 2 (by decide)))
  · change ev s [0, 3] = ev s [3, 0]
    exact (replaceWord s [] [0, 3] [3, 0] [] (hc 0 3 (by decide)))
  · change ev s [0, 4] = ev s [4, 0]
    exact (replaceWord s [] [0, 4] [4, 0] [] (hc 0 4 (by decide)))
  · change ev s [0, 1, 0] = ev s [1, 0, 1]
    exact (replaceWord s [] [0, 1, 0] [1, 0, 1] [] (hb 0 1 (by decide)))
  · change ev s [0, 1, 1] = ev s [0]
    exact (replaceWord s [0] [1, 1] [] [] (hs 1))
  · rfl
  · change ev s [0, 1, 3] = ev s [3, 0, 1]
    exact (replaceWord s [0] [1, 3] [3, 1] [] (hc 1 3 (by decide))).trans ((replaceWord s [] [0, 3] [3, 0] [1] (hc 0 3 (by decide))))
  · change ev s [0, 1, 4] = ev s [4, 0, 1]
    exact (replaceWord s [0] [1, 4] [4, 1] [] (hc 1 4 (by decide))).trans ((replaceWord s [] [0, 4] [4, 0] [1] (hc 0 4 (by decide))))
  · change ev s [0, 1, 2, 0] = ev s [1, 0, 1, 2]
    exact (replaceWord s [0, 1] [2, 0] [0, 2] [] (hc 2 0 (by decide))).trans ((replaceWord s [] [0, 1, 0] [1, 0, 1] [2] (hb 0 1 (by decide))))
  · change ev s [0, 1, 2, 1] = ev s [2, 0, 1, 2]
    exact (replaceWord s [0] [1, 2, 1] [2, 1, 2] [] (hb 1 2 (by decide))).trans ((replaceWord s [] [0, 2] [2, 0] [1, 2] (hc 0 2 (by decide))))
  · change ev s [0, 1, 2, 2] = ev s [0, 1]
    exact (replaceWord s [0, 1] [2, 2] [] [] (hs 2))
  · rfl
  · change ev s [0, 1, 2, 4] = ev s [4, 0, 1, 2]
    exact (replaceWord s [0, 1] [2, 4] [4, 2] [] (hc 2 4 (by decide))).trans ((replaceWord s [0] [1, 4] [4, 1] [2] (hc 1 4 (by decide))).trans ((replaceWord s [] [0, 4] [4, 0] [1, 2] (hc 0 4 (by decide)))))
  · change ev s [0, 1, 2, 3, 0] = ev s [1, 0, 1, 2, 3]
    exact (replaceWord s [0, 1, 2] [3, 0] [0, 3] [] (hc 3 0 (by decide))).trans ((replaceWord s [0, 1] [2, 0] [0, 2] [3] (hc 2 0 (by decide))).trans ((replaceWord s [] [0, 1, 0] [1, 0, 1] [2, 3] (hb 0 1 (by decide)))))
  · change ev s [0, 1, 2, 3, 1] = ev s [2, 0, 1, 2, 3]
    exact (replaceWord s [0, 1, 2] [3, 1] [1, 3] [] (hc 3 1 (by decide))).trans ((replaceWord s [0] [1, 2, 1] [2, 1, 2] [3] (hb 1 2 (by decide))).trans ((replaceWord s [] [0, 2] [2, 0] [1, 2, 3] (hc 0 2 (by decide)))))
  · change ev s [0, 1, 2, 3, 2] = ev s [3, 0, 1, 2, 3]
    exact (replaceWord s [0, 1] [2, 3, 2] [3, 2, 3] [] (hb 2 3 (by decide))).trans ((replaceWord s [0] [1, 3] [3, 1] [2, 3] (hc 1 3 (by decide))).trans ((replaceWord s [] [0, 3] [3, 0] [1, 2, 3] (hc 0 3 (by decide)))))
  · change ev s [0, 1, 2, 3, 3] = ev s [0, 1, 2]
    exact (replaceWord s [0, 1, 2] [3, 3] [] [] (hs 3))
  · rfl
  · change ev s [0, 1, 2, 3, 4, 0] = ev s [1, 0, 1, 2, 3, 4]
    exact (replaceWord s [0, 1, 2, 3] [4, 0] [0, 4] [] (hc 4 0 (by decide))).trans ((replaceWord s [0, 1, 2] [3, 0] [0, 3] [4] (hc 3 0 (by decide))).trans ((replaceWord s [0, 1] [2, 0] [0, 2] [3, 4] (hc 2 0 (by decide))).trans ((replaceWord s [] [0, 1, 0] [1, 0, 1] [2, 3, 4] (hb 0 1 (by decide))))))
  · change ev s [0, 1, 2, 3, 4, 1] = ev s [2, 0, 1, 2, 3, 4]
    exact (replaceWord s [0, 1, 2, 3] [4, 1] [1, 4] [] (hc 4 1 (by decide))).trans ((replaceWord s [0, 1, 2] [3, 1] [1, 3] [4] (hc 3 1 (by decide))).trans ((replaceWord s [0] [1, 2, 1] [2, 1, 2] [3, 4] (hb 1 2 (by decide))).trans ((replaceWord s [] [0, 2] [2, 0] [1, 2, 3, 4] (hc 0 2 (by decide))))))
  · change ev s [0, 1, 2, 3, 4, 2] = ev s [3, 0, 1, 2, 3, 4]
    exact (replaceWord s [0, 1, 2, 3] [4, 2] [2, 4] [] (hc 4 2 (by decide))).trans ((replaceWord s [0, 1] [2, 3, 2] [3, 2, 3] [4] (hb 2 3 (by decide))).trans ((replaceWord s [0] [1, 3] [3, 1] [2, 3, 4] (hc 1 3 (by decide))).trans ((replaceWord s [] [0, 3] [3, 0] [1, 2, 3, 4] (hc 0 3 (by decide))))))
  · change ev s [0, 1, 2, 3, 4, 3] = ev s [4, 0, 1, 2, 3, 4]
    exact (replaceWord s [0, 1, 2] [3, 4, 3] [4, 3, 4] [] (hb 3 4 (by decide))).trans ((replaceWord s [0, 1] [2, 4] [4, 2] [3, 4] (hc 2 4 (by decide))).trans ((replaceWord s [0] [1, 4] [4, 1] [2, 3, 4] (hc 1 4 (by decide))).trans ((replaceWord s [] [0, 4] [4, 0] [1, 2, 3, 4] (hc 0 4 (by decide))))))
  · change ev s [0, 1, 2, 3, 4, 4] = ev s [0, 1, 2, 3]
    exact (replaceWord s [0, 1, 2, 3] [4, 4] [] [] (hs 4))
  · exact False.elim ((by decide : ¬ (1 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (1 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (1 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (1 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (1 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (1 : Nat) ≤ 0) ha)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ (1 : Nat) ≤ 0) ha)
  · change ev s [1, 1] = ev s []
    exact (replaceWord s [] [1, 1] [] [] (hs 1))
  · rfl
  · change ev s [1, 3] = ev s [3, 1]
    exact (replaceWord s [] [1, 3] [3, 1] [] (hc 1 3 (by decide)))
  · change ev s [1, 4] = ev s [4, 1]
    exact (replaceWord s [] [1, 4] [4, 1] [] (hc 1 4 (by decide)))
  · exact False.elim ((by decide : ¬ (1 : Nat) ≤ 0) ha)
  · change ev s [1, 2, 1] = ev s [2, 1, 2]
    exact (replaceWord s [] [1, 2, 1] [2, 1, 2] [] (hb 1 2 (by decide)))
  · change ev s [1, 2, 2] = ev s [1]
    exact (replaceWord s [1] [2, 2] [] [] (hs 2))
  · rfl
  · change ev s [1, 2, 4] = ev s [4, 1, 2]
    exact (replaceWord s [1] [2, 4] [4, 2] [] (hc 2 4 (by decide))).trans ((replaceWord s [] [1, 4] [4, 1] [2] (hc 1 4 (by decide))))
  · exact False.elim ((by decide : ¬ (1 : Nat) ≤ 0) ha)
  · change ev s [1, 2, 3, 1] = ev s [2, 1, 2, 3]
    exact (replaceWord s [1, 2] [3, 1] [1, 3] [] (hc 3 1 (by decide))).trans ((replaceWord s [] [1, 2, 1] [2, 1, 2] [3] (hb 1 2 (by decide))))
  · change ev s [1, 2, 3, 2] = ev s [3, 1, 2, 3]
    exact (replaceWord s [1] [2, 3, 2] [3, 2, 3] [] (hb 2 3 (by decide))).trans ((replaceWord s [] [1, 3] [3, 1] [2, 3] (hc 1 3 (by decide))))
  · change ev s [1, 2, 3, 3] = ev s [1, 2]
    exact (replaceWord s [1, 2] [3, 3] [] [] (hs 3))
  · rfl
  · exact False.elim ((by decide : ¬ (1 : Nat) ≤ 0) ha)
  · change ev s [1, 2, 3, 4, 1] = ev s [2, 1, 2, 3, 4]
    exact (replaceWord s [1, 2, 3] [4, 1] [1, 4] [] (hc 4 1 (by decide))).trans ((replaceWord s [1, 2] [3, 1] [1, 3] [4] (hc 3 1 (by decide))).trans ((replaceWord s [] [1, 2, 1] [2, 1, 2] [3, 4] (hb 1 2 (by decide)))))
  · change ev s [1, 2, 3, 4, 2] = ev s [3, 1, 2, 3, 4]
    exact (replaceWord s [1, 2, 3] [4, 2] [2, 4] [] (hc 4 2 (by decide))).trans ((replaceWord s [1] [2, 3, 2] [3, 2, 3] [4] (hb 2 3 (by decide))).trans ((replaceWord s [] [1, 3] [3, 1] [2, 3, 4] (hc 1 3 (by decide)))))
  · change ev s [1, 2, 3, 4, 3] = ev s [4, 1, 2, 3, 4]
    exact (replaceWord s [1, 2] [3, 4, 3] [4, 3, 4] [] (hb 3 4 (by decide))).trans ((replaceWord s [1] [2, 4] [4, 2] [3, 4] (hc 2 4 (by decide))).trans ((replaceWord s [] [1, 4] [4, 1] [2, 3, 4] (hc 1 4 (by decide)))))
  · change ev s [1, 2, 3, 4, 4] = ev s [1, 2, 3]
    exact (replaceWord s [1, 2, 3] [4, 4] [] [] (hs 4))
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (2 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 1) ha)
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 1) ha)
  · change ev s [2, 2] = ev s []
    exact (replaceWord s [] [2, 2] [] [] (hs 2))
  · rfl
  · change ev s [2, 4] = ev s [4, 2]
    exact (replaceWord s [] [2, 4] [4, 2] [] (hc 2 4 (by decide)))
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 1) ha)
  · change ev s [2, 3, 2] = ev s [3, 2, 3]
    exact (replaceWord s [] [2, 3, 2] [3, 2, 3] [] (hb 2 3 (by decide)))
  · change ev s [2, 3, 3] = ev s [2]
    exact (replaceWord s [2] [3, 3] [] [] (hs 3))
  · rfl
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (2 : Nat) ≤ 1) ha)
  · change ev s [2, 3, 4, 2] = ev s [3, 2, 3, 4]
    exact (replaceWord s [2, 3] [4, 2] [2, 4] [] (hc 4 2 (by decide))).trans ((replaceWord s [] [2, 3, 2] [3, 2, 3] [4] (hb 2 3 (by decide))))
  · change ev s [2, 3, 4, 3] = ev s [4, 2, 3, 4]
    exact (replaceWord s [2] [3, 4, 3] [4, 3, 4] [] (hb 3 4 (by decide))).trans ((replaceWord s [] [2, 4] [4, 2] [3, 4] (hc 2 4 (by decide))))
  · change ev s [2, 3, 4, 4] = ev s [2, 3]
    exact (replaceWord s [2, 3] [4, 4] [] [] (hs 4))
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (3 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 1) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 2) ha)
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 1) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 2) ha)
  · change ev s [3, 3] = ev s []
    exact (replaceWord s [] [3, 3] [] [] (hs 3))
  · rfl
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 1) ha)
  · exact False.elim ((by decide : ¬ (3 : Nat) ≤ 2) ha)
  · change ev s [3, 4, 3] = ev s [4, 3, 4]
    exact (replaceWord s [] [3, 4, 3] [4, 3, 4] [] (hb 3 4 (by decide)))
  · change ev s [3, 4, 4] = ev s [3]
    exact (replaceWord s [3] [4, 4] [] [] (hs 4))
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 0) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 1) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 2) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 3) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 3) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 3) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 3) hr)
  · exact False.elim ((by decide : ¬ (4 : Fin 6) ≤ 3) hr)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 1) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 2) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 3) ha)
  · rfl
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 0) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 1) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 2) ha)
  · exact False.elim ((by decide : ¬ (4 : Nat) ≤ 3) ha)
  · change ev s [4, 4] = ev s []
    exact (replaceWord s [] [4, 4] [] [] (hs 4))
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)
  · exact False.elim ((by decide : ¬ (5 : Nat) < 5) hl)

@[expose] public def swapGen (a : Fin 5) : Equiv.Perm (Fin 6) :=
  Equiv.swap a.castSucc ⟨a.val + 1, by omega⟩

private def tailGroup (s : Fin 5 → G) (l : Nat) : Subgroup G :=
  closure (s '' {a | l ≤ a.val})

private theorem factor_mem (s : Fin 5 → G) (l r : Fin 6) (a : Fin 5)
    (hr : l ≤ r) (ha : l.val ≤ a.val) : ev s (factor r a) ∈ tailGroup s (l.val + 1) := by
  apply (tailGroup s (l.val + 1)).list_prod_mem
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  apply subset_closure
  refine ⟨b, ?_, rfl⟩
  have : l.val + 1 ≤ b.val := by
    unfold factor at hb
    split at hb
    · simp at hb
    · split at hb
      · simp only [List.mem_singleton] at hb
        subst b
        change l.val + 1 ≤ a.val + 1
        omega
      · simp only [List.mem_singleton] at hb
        subst b
        omega
  exact this

private theorem dest_ge (l r : Fin 6) (a : Fin 5) (hr : l ≤ r) (ha : l.val ≤ a.val) :
    l ≤ dest r a := by
  unfold dest
  split
  · change l.val ≤ a.val + 1
    omega
  · split
    · exact ha
    · exact hr

private theorem covers_tail (s : Fin 5 → G)
    (hs : ∀ a, ev s [a,a] = ev s [])
    (hc : ∀ a b : Fin 5, a.val + 1 < b.val ∨ b.val + 1 < a.val → ev s [a,b] = ev s [b,a])
    (hb : ∀ a b : Fin 5, a.val + 1 = b.val ∨ b.val + 1 = a.val → ev s [a,b,a] = ev s [b,a,b])
    (l : Fin 6) (hl : l.val < 5) {x : G} (hx : x ∈ tailGroup s l.val) :
    ∃ h ∈ tailGroup s (l.val + 1), ∃ r : Fin 6, l ≤ r ∧ x = h * ev s (repWord l r) := by
  have hrep : ev s (repWord l l) = 1 := by
    have hw : repWord l l = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      simp only [repWord, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at ha
      omega
    rw [hw, ev_nil]
  have hi (a : Fin 5) : (s a)⁻¹ = s a := by
    apply inv_eq_of_mul_eq_one_left
    simpa [ev] using hs a
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨1, one_mem _, l, le_rfl, by simp [hrep]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨h, hh, r, hr, rfl⟩ := ih
    refine ⟨h * ev s (factor r a), mul_mem hh (factor_mem s l r a hr ha),
      dest r a, dest_ge l r a hr ha, ?_⟩
    have ht := transitions s hs hc hb l r a hl hr ha
    rw [ev_append, ev_append] at ht
    simpa only [ev, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using congrArg (h * ·) ht
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨h, hh, r, hr, rfl⟩ := ih
    refine ⟨h * ev s (factor r a), mul_mem hh (factor_mem s l r a hr ha),
      dest r a, dest_ge l r a hr ha, ?_⟩
    rw [hi]
    have ht := transitions s hs hc hb l r a hl hr ha
    rw [ev_append, ev_append] at ht
    simpa only [ev, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using congrArg (h * ·) ht

private theorem ev_map (s : Fin 5 → G) (f : G →* Equiv.Perm (Fin 6)) (w : List (Fin 5)) :
    f (ev s w) = ev (fun a => f (s a)) w := by simp [ev, map_list_prod, List.map_map, Function.comp_def]

private theorem tail_fixes (s : Fin 5 → G) (f : G →* Equiv.Perm (Fin 6))
    (hf : ∀ a, f (s a) = swapGen a) (l : Fin 6) {h : G}
    (hh : h ∈ tailGroup s (l.val + 1)) : f h l = l := by
  have hle : tailGroup s (l.val + 1) ≤ (MulAction.stabilizer (Equiv.Perm (Fin 6)) l).comap f := by
    apply (closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    change f (s a) l = l
    rw [hf]
    have hc : ∀ (l : Fin 6) (a : Fin 5), l.val + 1 ≤ a.val → swapGen a l = l := by decide
    exact hc l a ha
  exact hle hh

private theorem kernel_descent (s : Fin 5 → G) (f : G →* Equiv.Perm (Fin 6))
    (hf : ∀ a, f (s a) = swapGen a)
    (hs : ∀ a, ev s [a,a] = ev s [])
    (hc : ∀ a b : Fin 5, a.val + 1 < b.val ∨ b.val + 1 < a.val → ev s [a,b] = ev s [b,a])
    (hb : ∀ a b : Fin 5, a.val + 1 = b.val ∨ b.val + 1 = a.val → ev s [a,b,a] = ev s [b,a,b])
    (l : Fin 6) (hl : l.val < 5) {x : G} (hx : x ∈ tailGroup s l.val) (hk : f x = 1) :
    x ∈ tailGroup s (l.val + 1) := by
  obtain ⟨h, hh, r, hr, he⟩ := covers_tail s hs hc hb l hl hx
  have hpoint : ev swapGen (repWord l r) r = l := by
    have hcheck : ∀ (l r : Fin 6), l ≤ r → ev swapGen (repWord l r) r = l := by decide
    exact hcheck l r hr
  have hrl : r = l := by
    have he' := congrArg (fun z : Equiv.Perm (Fin 6) => z r) (congrArg f he)
    rw [hk, map_mul, ev_map] at he'
    simp only [hf] at he'
    change r = f h (ev swapGen (repWord l r) r) at he'
    rw [hpoint, tail_fixes s f hf l hh] at he'
    exact he'
  subst r
  have hw : repWord l l = [] := by
    have hcheck : ∀ l : Fin 6, repWord l l = [] := by decide
    exact hcheck l
  rw [hw, ev_nil, mul_one] at he
  exact he ▸ hh

public theorem faithful_of_relations (s : Fin 5 → G) (f : G →* Equiv.Perm (Fin 6))
    (hg : closure (Set.range s) = ⊤) (hf : ∀ a, f (s a) = swapGen a)
    (hs : ∀ a, ev s [a,a] = ev s [])
    (hc : ∀ a b : Fin 5, a.val + 1 < b.val ∨ b.val + 1 < a.val → ev s [a,b] = ev s [b,a])
    (hb : ∀ a b : Fin 5, a.val + 1 = b.val ∨ b.val + 1 = a.val → ev s [a,b,a] = ev s [b,a,b])
    {x : G} (hx : f x = 1) : x = 1 := by
  have h0 : x ∈ tailGroup s 0 := by simp [tailGroup, hg]
  have h1 := kernel_descent s f hf hs hc hb 0 (by decide) h0 hx
  have h2 := kernel_descent s f hf hs hc hb 1 (by decide) h1 hx
  have h3 := kernel_descent s f hf hs hc hb 2 (by decide) h2 hx
  have h4 := kernel_descent s f hf hs hc hb 3 (by decide) h3 hx
  have h5 := kernel_descent s f hf hs hc hb 4 (by decide) h4 hx
  have ht : tailGroup s 5 = ⊥ := by
    have he : {a : Fin 5 | 5 ≤ a.val} = ∅ := by ext a; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; omega
    simp [tailGroup, he]
  simpa only [show (4 : Fin 6).val + 1 = 5 from rfl, ht, mem_bot] using h5

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound
