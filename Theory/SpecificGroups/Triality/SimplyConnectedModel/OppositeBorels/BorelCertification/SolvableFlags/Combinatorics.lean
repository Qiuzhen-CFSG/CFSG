module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Order ideals for the eight weights of the natural D4 module

The positive simple roots give a chain with a diamond in the middle. Its
order ideals are precisely the initial segments of the usual order or the
order with the two middle positions interchanged. The proof separates the
ten possible ideals instead of enumerating all subsets of eight positions.

This is the finite combinatorial step for the concrete Borel candidates in
GLS3, 1.11.2 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section

namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags.Combinatorics

def Edge (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
  (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) ∨
  (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 7)

instance edgeDecidable (i j : Fin 8) : Decidable (Edge i j) := inferInstanceAs (Decidable (_ ∨ _))

def initial (alternate : Bool) (r : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun i =>
    ((if alternate then Equiv.swap 3 4 i else i) : Fin 8).val < r

theorem initial_of_closed (I : Finset (Fin 8))
    (h : ∀ i j, Edge i j → j ∈ I → i ∈ I) :
      ∃ alternate : Bool, I = initial alternate I.card := by
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h23 := h 2 3 (by decide)
  have h24 := h 2 4 (by decide)
  have h35 := h 3 5 (by decide)
  have h45 := h 4 5 (by decide)
  have h56 := h 5 6 (by decide)
  have h67 := h 6 7 (by decide)
  by_cases h7 : 7 ∈ I
  · have heq : I = {0, 1, 2, 3, 4, 5, 6, 7} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h6 : 6 ∈ I
  · have heq : I = {0, 1, 2, 3, 4, 5, 6} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h5 : 5 ∈ I
  · have heq : I = {0, 1, 2, 3, 4, 5} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h4 : 4 ∈ I
  · by_cases h3 : 3 ∈ I
    · have heq : I = {0, 1, 2, 3, 4} := by
        ext i
        fin_cases i <;> simp_all
      rw [heq]
      exact ⟨false, by decide⟩
    · have heq : I = {0, 1, 2, 4} := by
        ext i
        fin_cases i <;> simp_all
      rw [heq]
      exact ⟨true, by decide⟩
  by_cases h3 : 3 ∈ I
  · have heq : I = {0, 1, 2, 3} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h2 : 2 ∈ I
  · have heq : I = {0, 1, 2} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h1 : 1 ∈ I
  · have heq : I = {0, 1} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  by_cases h0 : 0 ∈ I
  · have heq : I = {0} := by
      ext i
      fin_cases i <;> simp_all
    rw [heq]
    exact ⟨false, by decide⟩
  have heq : I = ∅ := by
    ext i
    fin_cases i <;> simp_all
  rw [heq]
  exact ⟨false, by decide⟩

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags.Combinatorics
