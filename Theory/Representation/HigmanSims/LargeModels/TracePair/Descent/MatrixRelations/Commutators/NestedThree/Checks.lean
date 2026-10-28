module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming
public import Mathlib.Tactic.FinCases

/-!
# Bounded checks for the nested HS commutator

Saved rows are used only after their products have been checked in Lean.
`run_step` composes the original 42-letter coordinate trace. `InRange.append`
joins adjacent intervals of separately checked matrix-product rows, so a large
certificate can be compiled in bounded pieces. The numerical producers must
cover every coordinate before applying the existing streaming matrix lemmas.

Source: the literal `(a,b*a*b)^3` in `Descent/source/HSG1-P1.M` and the
unchanged HSG1-f4r896aB0 matrices retained in `TracePair/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree
open Certificates Streaming

theorem run_step (a b z : Packed.Row) (c : Bool) (cs : List Bool)
    (h : product a (letterRows c) = b) (hz : run b cs = z) :
    run a (c :: cs) = z := by
  rw [run, h]
  exact hz

/-- Natural-number indexing avoids elaborating a large power through a `Fin` cast. -/
theorem word_row_of_check (cs : List Bool) (i : ℕ) (hi : i < 896)
    (h : run (2 ^ i, 0) cs = (2 ^ i, 0)) :
    (cs.map letterMatrix).prod ⟨i, hi⟩ =
      (1 : Matrix (Fin 896) (Fin 896) Four) ⟨i, hi⟩ :=
  word_row_eq_of_run cs ⟨i, hi⟩ h

/-- The indexed claims in the half-open interval `[start, start + count)`. -/
def InRange (start count : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ j : Fin count, P (start + j.val)

theorem InRange.append {start left right : ℕ} {P : ℕ → Prop}
    (hl : InRange start left P) (hr : InRange (start + left) right P) :
    InRange start (left + right) P := by
  intro j
  by_cases hj : j.val < left
  · exact hl ⟨j.val, hj⟩
  · have hj' : j.val - left < right := by omega
    have he : start + left + (j.val - left) = start + j.val := by omega
    simpa only [he] using hr ⟨j.val - left, hj'⟩

theorem InRange.all {n : ℕ} {P : ℕ → Prop} (h : InRange 0 n P) :
    ∀ i : Fin n, P i.val := by
  intro i
  simpa only [Nat.zero_add] using h i

/-- A single inverse-product check gives the actual corresponding matrix row. -/
theorem inverse_row_of_check (a b : Packed.Mat) (i : ℕ) (hi : i < 896)
    (hb : b.length = 896)
    (h : product (a.getD i (0, 0)) b = (2 ^ i, 0)) :
    (Packed.eval 896 a * Packed.eval 896 b) ⟨i, hi⟩ =
      (1 : Matrix (Fin 896) (Fin 896) Four) ⟨i, hi⟩ := by
  change Matrix.vecMul (vector (a.getD i (0, 0))) (Packed.eval 896 b) = _
  rw [← vector_product _ _ hb, h]
  simpa only [Matrix.vecMul_one] using
    vecMul_basis (1 : Matrix (Fin 896) (Fin 896) Four) ⟨i, hi⟩

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree
