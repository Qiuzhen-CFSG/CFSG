module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.Root

/-! 
# Batched checks for the Lyons plane tree

This module provides the executable boundary used by a complete orbit-data
certificate.  The checks are deliberately propositions compiled through
`decide`: their soundness is established here once, while large data modules
only need to provide closed Boolean equalities.  Reduced-shape checks and
sorting checks remain independent of the edge matrix arithmetic.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitData
open Matrix

/-- Check the first `n` base-eight digits without repeatedly dividing by powers. -/
def checkCanonicalDigits : ℕ → ℕ → Bool
  | 0, x => decide (x = 0)
  | n + 1, x => decide (x % 8 < 5) && checkCanonicalDigits n (x / 8)

private theorem canonicalDigits_of_check (n x : ℕ)
    (h : checkCanonicalDigits n x = true) :
    x < 8 ^ n ∧ ∀ r < n, digit x r < 5 := by
  induction n generalizing x with
  | zero =>
    have hx : x = 0 := by
      simpa only [checkCanonicalDigits] using of_decide_eq_true h
    subst x
    simp [digit]
  | succ n ih =>
    change (decide (x % 8 < 5) && checkCanonicalDigits n (x / 8)) = true at h
    have hparts := (Bool.and_eq_true _ _).mp h
    have hdigit : x % 8 < 5 := by
      exact of_decide_eq_true hparts.1
    have htail := ih (x / 8) hparts.2
    constructor
    · calc
        x = x % 8 + 8 * (x / 8) := (Nat.mod_add_div x 8).symm
        _ < 8 * 8 ^ n := by omega
        _ = 8 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]
    · intro r hr
      rcases r with _ | r
      · simpa [digit] using hdigit
      · simpa only [digit, Nat.div_div_eq_div_mul, pow_succ'] using htail.2 r (by omega)

/-- Check that one packed column has canonical base-eight digits. -/
def checkValidColumn (x : ℕ) : Bool := checkCanonicalDigits 111 x

theorem validColumn_of_check {x : ℕ} (h : checkValidColumn x = true) :
    ValidColumn x := by
  have hc := canonicalDigits_of_check 111 x h
  exact ⟨hc.1, fun r => hc.2 r.val r.isLt⟩

/-- Check canonical digits in every column of every node in a finite batch. -/
def checkValidRows {n : ℕ} (rows : Fin n → PackedRows) : Bool :=
  decide (∀ i j, checkValidColumn (rows i j) = true)

theorem validRows_of_check {n : ℕ} {rows : Fin n → PackedRows}
    (h : checkValidRows rows = true) :
    ∀ i j, ValidColumn (rows i j) := by
  have hc : ∀ i j, checkValidColumn (rows i j) = true := by
    simpa only [checkValidRows] using of_decide_eq_true h
  exact fun i j => validColumn_of_check (hc i j)

/-- The first-column specialization used by the sorted distinctness check. -/
def checkValidFirstColumns {n : ℕ} (rows : Fin n → PackedRows) : Bool :=
  decide (∀ i, checkValidColumn (rows i 0) = true)

theorem validFirstColumns_of_check {n : ℕ} {rows : Fin n → PackedRows}
    (h : checkValidFirstColumns rows = true) :
    ∀ i, ValidColumn (rows i 0) := by
  have hc : ∀ i, checkValidColumn (rows i 0) = true := by
    simpa only [checkValidFirstColumns] using of_decide_eq_true h
  exact fun i => validColumn_of_check (hc i)

/-- Check reduced-column shape independently at every node of a batch. -/
def checkReducedBatch {n : ℕ} (rows : Fin n → PackedRows)
    (pivot : Fin n → Fin 7 → Fin 111) : Bool :=
  decide (∀ i, checkReduced (rows i) (pivot i) = true)

def reducedBasis_of_batch_check {n : ℕ} {rows : Fin n → PackedRows}
    {pivot : Fin n → Fin 7 → Fin 111}
    (h : checkReducedBatch rows pivot = true) :
    ∀ i, ReducedColumnBasis (columns (rows i)) := by
  have hb : ∀ i, checkReduced (rows i) (pivot i) = true := by
    simpa only [checkReducedBatch] using of_decide_eq_true h
  intro i
  exact reducedBasisOfCheck (hb i)

/-- Check the adjacent strict inequalities in a sorted first-column order. -/
def checkAdjacentFirstColumn {n : ℕ}
    (rows : Fin (n + 1) → PackedRows) (order : Fin (n + 1) → Fin (n + 1)) : Bool :=
  decide (∀ i : Fin n,
    rows (order i.castSucc) 0 < rows (order i.succ) 0)

theorem adjacentFirstColumn_of_check {n : ℕ}
    {rows : Fin (n + 1) → PackedRows} {order : Fin (n + 1) → Fin (n + 1)}
    (h : checkAdjacentFirstColumn rows order = true) :
    ∀ i : Fin n, rows (order i.castSucc) 0 < rows (order i.succ) 0 := by
  simpa only [checkAdjacentFirstColumn] using of_decide_eq_true h

/-- A first-column batch certificate directly yields matrix injectivity. -/
theorem columns_injective_of_batch_checks {n : ℕ}
    (rows : Fin (n + 1) → PackedRows) (order : Fin (n + 1) → Fin (n + 1))
    (hvalid : checkValidFirstColumns rows = true)
    (hadjacent : checkAdjacentFirstColumn rows order = true) :
    Function.Injective (fun i => columns (rows i)) := by
  exact columns_injective_of_adjacent rows order
    (validFirstColumns_of_check hvalid)
    (adjacentFirstColumn_of_check hadjacent)

/-- A full-key batch certificate is the fallback when first columns collide. -/
def checkFullKeySorted {n : ℕ}
    (rows : Fin n → PackedRows) (order : Fin n → Fin n) : Bool :=
  decide (StrictMono (fun i => fullKey (rows (order i))))

theorem fullKeySorted_of_check {n : ℕ}
    {rows : Fin n → PackedRows} {order : Fin n → Fin n}
    (h : checkFullKeySorted rows order = true) :
    StrictMono (fun i => fullKey (rows (order i))) := by
  simpa only [checkFullKeySorted] using of_decide_eq_true h

theorem columns_injective_of_fullKey_batch_checks {n : ℕ}
    (rows : Fin n → PackedRows) (order : Fin n → Fin n)
    (hvalid : checkValidRows rows = true)
    (hsorted : checkFullKeySorted rows order = true) :
    Function.Injective (fun i => columns (rows i)) := by
  exact columns_injective_of_fullKey_sorted rows order
    (validRows_of_check hvalid) (fullKeySorted_of_check hsorted)

end Lyons.OrderCertificate.PlaneOrbitData
