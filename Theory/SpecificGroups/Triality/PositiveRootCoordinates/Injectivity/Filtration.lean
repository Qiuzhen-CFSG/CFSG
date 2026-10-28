module
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-!
# Matrix filtration for positive-root products

A matrix raises a real-valued degree by at least h if entries below that shift
vanish. Products add these bounds. Consequently, a product of matrices that
are identity modulo a positive degree h agrees with the sum of its linear
terms through degree h; all cross terms have degree at least 2h.

This is the matrix-filtration step in the positive-root uniqueness argument
of GLS3, 1.12.7 and 2.3.6–7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open scoped BigOperators
namespace Triality.Standard.PositiveCoordinates.Injectivity
noncomputable section
variable {I S : Type*} [Fintype I] [DecidableEq I] [CommRing S] (d : I → ℝ)

def Raises (h : ℝ) (A : Matrix I I S) : Prop :=
  ∀ i j, d i < h + d j → A i j = 0

omit [Fintype I] [DecidableEq I] in
lemma raises_zero (h : ℝ) : Raises d h (0 : Matrix I I S) := by
  intro i j _
  rfl

omit [Fintype I] [DecidableEq I] in
lemma Raises.mono {h k : ℝ} {A : Matrix I I S} (hA : Raises d h A)
    (hkh : k ≤ h) : Raises d k A := by
  intro i j hij
  apply hA i j
  linarith

omit [Fintype I] [DecidableEq I] in
lemma Raises.add {h : ℝ} {A B : Matrix I I S}
    (hA : Raises d h A) (hB : Raises d h B) : Raises d h (A + B) := by
  intro i j hij
  change A i j + B i j = 0
  rw [hA i j hij, hB i j hij, zero_add]

omit [Fintype I] [DecidableEq I] in
lemma Raises.smul {h : ℝ} {A : Matrix I I S}
    (hA : Raises d h A) (t : S) : Raises d h (t • A) := by
  intro i j hij
  change t * A i j = 0
  rw [hA i j hij, mul_zero]

omit [DecidableEq I] in
lemma Raises.mul {h k : ℝ} {A B : Matrix I I S}
    (hA : Raises d h A) (hB : Raises d k B) : Raises d (h + k) (A * B) := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro l _
  by_cases hil : d i < h + d l
  · simp [hA i l hil]
  · have hlj : d l < k + d j := by linarith
    simp [hB l j hlj]

lemma raises_prod_sub_one (h : ℝ) (hh : 0 ≤ h) (l : List (Matrix I I S))
    (hl : ∀ A ∈ l, Raises d h (A - 1)) : Raises d h (l.prod - 1) := by
  induction l with
  | nil => simpa using raises_zero d h
  | cons A l ih =>
      have hA := hl A (by simp)
      have hB := ih (fun B hB => hl B (by simp [hB]))
      have hAB := (hA.mul d hB).mono d (show h ≤ h + h by linarith)
      have heq : (A :: l).prod - 1 =
          (A - 1) + (l.prod - 1) + (A - 1) * (l.prod - 1) := by
        simp only [List.prod_cons]
        noncomm_ring
      rw [heq]
      exact (hA.add d hB).add d hAB

/-- Above a positive cutoff, every nonlinear term has at least twice that degree. -/
lemma raises_prod_remainder (h : ℝ) (hh : 0 ≤ h) (l : List (Matrix I I S))
    (hl : ∀ A ∈ l, Raises d h (A - 1)) :
    Raises d (h + h) (l.prod - 1 - (l.map (fun A => A - 1)).sum) := by
  induction l with
  | nil => simpa using raises_zero d (h + h)
  | cons A l ih =>
      have htail : ∀ B ∈ l, Raises d h (B - 1) := fun B hB => hl B (by simp [hB])
      have hAB := (hl A (by simp)).mul d (raises_prod_sub_one d h hh l htail)
      have heq : (A :: l).prod - 1 - ((A :: l).map (fun A => A - 1)).sum =
          (A - 1) * (l.prod - 1) + (l.prod - 1 - (l.map (fun A => A - 1)).sum) := by
        simp only [List.prod_cons, List.map_cons, List.sum_cons]
        noncomm_ring
      rw [heq]
      exact hAB.add d (ih htail)

omit [Fintype I] [DecidableEq I] in
lemma list_sum_entry_zero (l : List (Matrix I I S)) (i j : I)
    (hl : ∀ A ∈ l, A i j = 0) : l.sum i j = 0 := by
  induction l with
  | nil => rfl
  | cons A l ih =>
      change A i j + l.sum i j = 0
      rw [hl A (by simp), ih (fun B hB => hl B (by simp [hB])), zero_add]

lemma prod_entry_eq_sum (h : ℝ) (hh : 0 < h) (l : List (Matrix I I S))
    (hl : ∀ A ∈ l, Raises d h (A - 1)) (i j : I) (hij : d i ≤ h + d j) :
    l.prod i j = (1 : Matrix I I S) i j +
      ((l.map (fun A : Matrix I I S => A - 1)).sum : Matrix I I S) i j := by
  have he := raises_prod_remainder d h hh.le l hl i j (by linarith)
  change l.prod i j - (1 : Matrix I I S) i j - _ = 0 at he
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

end
end Triality.Standard.PositiveCoordinates.Injectivity
