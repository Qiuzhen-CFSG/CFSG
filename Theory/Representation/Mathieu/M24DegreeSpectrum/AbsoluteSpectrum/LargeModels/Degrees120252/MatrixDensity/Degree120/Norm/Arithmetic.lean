module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Data120
/-!
# Checked suffix sums for packed binary row products

A certificate lists the XOR suffix sums of the rows selected by a binary mask.
The recursive checker verifies each individual XOR on supplied natural numbers,
and list induction identifies its output with the existing packed decoder.
This avoids repeatedly reducing nested XOR expressions in a dense product.
Checked row blocks concatenate through `append_rows` without reevaluation.

These helpers are used by `Norm.Products` for the literal node-19 expression
from `Degrees120252/source/density-120.json`. The ATLAS matrices and all published
data are unchanged. Candidate suffix sums are untrusted data, checked by Lean.
-/

@[expose] public section
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm

private def combineFast : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: l, mask =>
      (if mask % 2 = 1 then a else 0) ^^^ combineFast l (mask / 2)

private theorem combineFast_from (l : List ℕ) (mask start : ℕ) :
    combineFast l (mask >>> start) = combineListFrom l mask start := by
  induction l generalizing start with
  | nil => rfl
  | cons a l ih =>
    rw [combineFast, combineListFrom, ← Nat.shiftRight_succ, ih]
    have hb : (mask >>> start).testBit 0 = mask.testBit start := by simp
    simp only [Nat.testBit_zero] at hb
    congr 1
    split_ifs <;> simp_all

private theorem combineFast_eq (l : List ℕ) (mask : ℕ) :
    combineFast l mask = combineList l mask := by
  exact combineFast_from l mask 0

private theorem map_fast {a b c : List ℕ} (h : a.map (combineFast b) = c) :
    a.map (combineList b) = c := by
  rw [show combineFast b = combineList b from funext (combineFast_eq b)] at h
  exact h

/-- Suffix sums are supplied as data; each selected row needs one small XOR check. -/
def checkRow : List ℕ → ℕ → List ℕ → Bool
  | [], _, sums => sums.headD 0 == 0
  | a :: l, mask, sums =>
    if mask % 2 = 1 then
      (sums.headD 0 == Nat.xor a (sums.tail.headD 0)) &&
        checkRow l (mask / 2) sums.tail
    else checkRow l (mask / 2) sums

private theorem checkRow_sound (l : List ℕ) (mask : ℕ) (sums : List ℕ)
    (h : checkRow l mask sums = true) :
    combineFast l mask = sums.headD 0 := by
  induction l generalizing mask sums with
  | nil =>
    have he : sums.headD 0 = 0 := by simpa only [checkRow, beq_iff_eq] using h
    exact he.symm
  | cons a l ih =>
    by_cases hm : mask % 2 = 1
    · simp only [checkRow, if_pos hm, Bool.and_eq_true, beq_iff_eq] at h
      rw [combineFast, if_pos hm, ih _ _ h.2]
      exact h.1.symm
    · simp only [checkRow, if_neg hm] at h
      rw [combineFast, if_neg hm, Nat.zero_xor]
      exact ih _ _ h

def checkRows (b : List ℕ) : List ℕ → List ℕ → List (List ℕ) → Bool
  | [], [], [] => true
  | a :: as, c :: cs, s :: ss =>
    (s.headD 0 == c) && checkRow b a s && checkRows b as cs ss
  | _, _, _ => false

private theorem checkRows_sound (b a c : List ℕ) (s : List (List ℕ))
    (h : checkRows b a c s = true) : a.map (combineFast b) = c := by
  induction a generalizing c s with
  | nil => cases c <;> cases s <;> simp_all [checkRows]
  | cons a as ih =>
    cases c with
    | nil => cases s <;> simp_all [checkRows]
    | cons c cs =>
      cases s with
      | nil => simp_all [checkRows]
      | cons s ss =>
        simp only [checkRows, Bool.and_eq_true, beq_iff_eq] at h
        rw [List.map_cons, checkRow_sound b a s h.1.2, h.1.1, ih _ _ h.2]

theorem certified_product (b a c : List ℕ) (s : List (List ℕ))
    (h : checkRows b a c s = true) : a.map (combineList b) = c :=
  map_fast (checkRows_sound b a c s h)

/-- Join already checked row blocks without evaluating their matrix products again. -/
theorem append_rows {b a₁ a₂ c₁ c₂ : List ℕ}
    (h₁ : a₁.map (combineList b) = c₁) (h₂ : a₂.map (combineList b) = c₂) :
    (a₁ ++ a₂).map (combineList b) = c₁ ++ c₂ := by
  rw [List.map_append, h₁, h₂]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm
