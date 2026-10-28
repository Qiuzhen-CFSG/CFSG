module

public import Mathlib.Data.List.GetD

/-!
# Linear checks of the orbit-tree metadata

A list recursion checks each parent against its zero-based position exactly
once. Its correctness theorem supplies the indexed inequalities used by orbit
induction. This avoids recomputing long list prefixes inside a finite universal
quantifier. The literal source arrays are in `ColumnData` and `RowData`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

def parentCheck : List ℕ → ℕ → Bool
  | [], _ => true
  | p :: ps, k => decide (p ≤ k) && parentCheck ps (k + 1)

theorem parentCheck_getD (ps : List ℕ) (k : ℕ) (h : parentCheck ps k = true)
    (i : ℕ) (hi : i < ps.length) : ps.getD i 0 ≤ k + i := by
  induction ps generalizing k i with
  | nil => simp at hi
  | cons p ps ih =>
    simp only [parentCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < ps.length := by simpa using hi
      simpa only [List.getD_cons_succ, Nat.add_right_comm, Nat.add_assoc,
        Nat.succ_eq_add_one] using ih (k + 1) h.2 i hi'

theorem letterCheck_getD (ps : List ℕ) (h : ps.all (fun p => decide (p ≤ 1)) = true)
    (i : ℕ) (hi : i < ps.length) : ps.getD i 0 ≤ 1 := by
  have hm : ps.getD i 0 ∈ ps := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  exact of_decide_eq_true (List.all_eq_true.mp h _ hm)

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans
