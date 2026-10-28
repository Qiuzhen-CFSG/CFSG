/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/TriplePermutation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.FinRange
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic

/-!
# TriplePermutation

Permutations of three coordinates are characterized by permutations of their
three-entry lists. The proof enumerates the six possible reorderings.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/TriplePermutation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas
open scoped Matrix

theorem triple_perm_reindex {α : Type*} (p : Equiv.Perm (Fin 3)) (f : Fin 3 → α) :
    List.Perm [f (p.symm 0),f (p.symm 1),f (p.symm 2)] [f 0,f 1,f 2] := by
  simpa [List.ofFn_succ] using Equiv.Perm.ofFn_comp_perm p.symm f

theorem triple_list_perm_cases {α : Type*} (a b c u v w : α)
    (h : List.Perm [u,v,w] [a,b,c]) :
    [u,v,w]=[a,b,c] ∨ [u,v,w]=[b,a,c] ∨ [u,v,w]=[c,b,a] ∨
    [u,v,w]=[b,c,a] ∨ [u,v,w]=[c,a,b] ∨ [u,v,w]=[a,c,b] := by
  have pair {v w a b : α} (h : List.Perm [v,w] [a,b]) :
      (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
    have hm := h.mem_iff.mp List.mem_cons_self
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ha | hb
    · subst v
      left
      exact ⟨rfl,by simpa using h.cons_inv⟩
    · subst v
      right
      exact ⟨rfl,by simpa using (h.trans (List.Perm.swap b a [])).cons_inv⟩
  have hm := h.mem_iff.mp List.mem_cons_self
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  simp only [List.cons.injEq]
  rcases hm with ha | hb | hc
  · subst u
    have hp := pair h.cons_inv
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · subst u
    have hp := pair (h.trans (List.Perm.swap b a [c])).cons_inv
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · subst u
    have ht : List.Perm [a,b,c] [c,a,b] :=
      (List.Perm.cons a (List.Perm.swap c b [])).trans (List.Perm.swap c a [b])
    have hp := pair (h.trans ht).cons_inv
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem triple_perm_exists {α : Type*} (f g : Fin 3 → α)
    (h : List.Perm [f 0,f 1,f 2] [g 0,g 1,g 2]) :
    ∃ p : Equiv.Perm (Fin 3),∀ i,f i=g (p.symm i) := by
  have hc := triple_list_perm_cases (g 0) (g 1) (g 2) (f 0) (f 1) (f 2) h
  rcases hc with h | h | h | h | h | h
  · refine ⟨1,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  · refine ⟨Equiv.swap 0 1,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i <;> simp <;> tauto
  · refine ⟨Equiv.swap 0 2,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i <;> simp <;> tauto
  · refine ⟨Equiv.swap 0 1*Equiv.swap 0 2,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i <;> simp <;> tauto
  · refine ⟨Equiv.swap 0 2*Equiv.swap 0 1,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i <;> simp <;> tauto
  · refine ⟨Equiv.swap 1 2,?_⟩
    simp only [List.cons.injEq] at h
    intro i
    fin_cases i <;> simp <;> tauto

end Atlas
