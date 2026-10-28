module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A checked 27-coordinate cubic and its twelve transvections

This module gives a 45-term cubic with coefficients ±1, normalized to take the
value one on the vector supported at coordinates 0, 9, 26. Each of the twelve
explicit signed simple transvections preserves the cubic. These are direct
commutative-ring identities; no division or characteristic restriction occurs.
Preservation passes to the actual free-word evaluation. A scalar word value
therefore has cube one.

The coordinate table lists twice the E7 roots with `r₀ + r₁ = 0` and
`r₁ - r₂ = -1`, in lexicographic order. The source table records addition or
subtraction of the first six simple roots. The assertions in this module concern
the displayed coordinate transformations. Their identification with the literal
Geck blocks in E7 and E8 is a separate representation calculation, consumed by
`CubicInvariant`; it is not assumed as a property of the table.

This supplies the integral cubic calculation for the E6 central-character bound
in GLS3 §§1.12.5–6 and the common-lattice subsystem construction in §2.6.2
(`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`), used in
Aschbacher–Smith A.2.17, printed p.39. The table and polynomial were computed
from the coordinate roots; all twelve polynomial identities below are checked
by Lean's kernel.
-/

@[expose] public section
open scoped Matrix
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.CubicModel
/-- Doubled root coordinates, in lexicographic order. The concrete E7/E8 block maps
use these vectors divided by two in the real root space, before specialization to a field. -/
def twiceRoot : Fin 27 → Fin 8 → ℤ :=
  ![![0, 0, 2, -2, 0, 0, 0, 0],
    ![0, 0, 2, 0, -2, 0, 0, 0],
    ![0, 0, 2, 0, 0, -2, 0, 0],
    ![0, 0, 2, 0, 0, 0, -2, 0],
    ![0, 0, 2, 0, 0, 0, 0, -2],
    ![0, 0, 2, 0, 0, 0, 0, 2],
    ![0, 0, 2, 0, 0, 0, 2, 0],
    ![0, 0, 2, 0, 0, 2, 0, 0],
    ![0, 0, 2, 0, 2, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 0, 0],
    ![1, -1, 1, -1, -1, -1, -1, -1],
    ![1, -1, 1, -1, -1, -1, 1, 1],
    ![1, -1, 1, -1, -1, 1, -1, 1],
    ![1, -1, 1, -1, -1, 1, 1, -1],
    ![1, -1, 1, -1, 1, -1, -1, 1],
    ![1, -1, 1, -1, 1, -1, 1, -1],
    ![1, -1, 1, -1, 1, 1, -1, -1],
    ![1, -1, 1, -1, 1, 1, 1, 1],
    ![1, -1, 1, 1, -1, -1, -1, 1],
    ![1, -1, 1, 1, -1, -1, 1, -1],
    ![1, -1, 1, 1, -1, 1, -1, -1],
    ![1, -1, 1, 1, -1, 1, 1, 1],
    ![1, -1, 1, 1, 1, -1, -1, -1],
    ![1, -1, 1, 1, 1, -1, 1, 1],
    ![1, -1, 1, 1, 1, 1, -1, 1],
    ![1, -1, 1, 1, 1, 1, 1, -1],
    ![2, -2, 0, 0, 0, 0, 0, 0]]

/-- Source of the unique nonzero entry of each row of a signed minuscule root operator. -/
def source (s : Bool) (i : Fin 6) : Fin 27 → Option (Fin 27) :=
  if s then
    ![![none, none, none, none, none, none, none, none, none, none, some 4, some 6, some 7, none, some 8, none, none, none, some 9, none, none, none, none, none, none, none, some 25],
      ![none, none, none, none, some 3, none, some 5, none, none, none, none, none, none, some 12, none, some 14, none, none, none, some 18, none, none, none, none, none, some 24, none],
      ![none, none, none, some 2, none, none, none, some 6, none, none, none, none, some 11, none, none, none, some 15, none, none, none, some 19, none, none, none, some 23, none, none],
      ![none, none, none, none, none, some 3, some 4, none, none, none, none, some 10, none, none, none, none, none, some 16, none, none, none, some 20, none, some 22, none, none, none],
      ![none, none, some 1, none, none, none, none, none, some 7, none, none, none, none, none, some 12, some 13, none, none, none, none, none, none, some 20, some 21, none, none, none],
      ![none, some 0, none, none, none, none, none, none, none, some 8, none, none, none, none, none, none, none, none, some 14, some 15, some 16, some 17, none, none, none, none, none]]
      i
  else
    ![![none, none, none, none, some 10, none, some 11, some 12, some 14, some 18, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, some 26, none],
      ![none, none, none, some 4, none, some 6, none, none, none, none, none, none, some 13, none, some 15, none, none, none, some 19, none, none, none, none, none, some 25, none, none],
      ![none, none, some 3, none, none, none, some 7, none, none, none, none, some 12, none, none, none, some 16, none, none, none, some 20, none, none, none, some 24, none, none, none],
      ![none, none, none, some 5, some 6, none, none, none, none, none, some 11, none, none, none, none, none, some 17, none, none, none, some 21, none, some 23, none, none, none, none],
      ![none, some 2, none, none, none, none, none, some 8, none, none, none, none, some 14, some 15, none, none, none, none, none, none, some 22, some 23, none, none, none, none, none],
      ![some 1, none, none, none, none, none, none, none, some 9, none, none, none, none, none, some 18, some 19, some 20, some 21, none, none, none, none, none, none, none, none, none]]
      i

variable {R : Type*} [CommRing R]
def operator (s : Bool) (i : Fin 6) : (Fin 27 → R) →ₗ[R] (Fin 27 → R) where
  toFun x r := match source s i r with | none => 0 | some j => x j
  map_add' x y := by funext r; cases h : source s i r <;> simp [h]
  map_smul' t x := by funext r; cases h : source s i r <;> simp [h]

def curve (s : Bool) (i : Fin 6) (t : R) (x : Fin 27 → R) : Fin 27 → R :=
  x + t • operator s i x

/-- The 45-term integral cubic, normalized at coordinates 0, 9, 26. -/
def cubic (x : Fin 27 → R) : R :=
  x 0 * x 9 * x 26
    - x 0 * x 18 * x 25
    + x 0 * x 19 * x 24
    - x 0 * x 20 * x 23
    + x 0 * x 21 * x 22
    - x 1 * x 8 * x 26
    + x 1 * x 14 * x 25
    - x 1 * x 15 * x 24
    + x 1 * x 16 * x 23
    - x 1 * x 17 * x 22
    + x 2 * x 7 * x 26
    - x 2 * x 12 * x 25
    + x 2 * x 13 * x 24
    - x 2 * x 16 * x 21
    + x 2 * x 17 * x 20
    - x 3 * x 6 * x 26
    + x 3 * x 11 * x 25
    - x 3 * x 13 * x 23
    + x 3 * x 15 * x 21
    - x 3 * x 17 * x 19
    + x 4 * x 5 * x 26
    - x 4 * x 11 * x 24
    + x 4 * x 12 * x 23
    - x 4 * x 14 * x 21
    + x 4 * x 17 * x 18
    - x 5 * x 10 * x 25
    + x 5 * x 13 * x 22
    - x 5 * x 15 * x 20
    + x 5 * x 16 * x 19
    + x 6 * x 10 * x 24
    - x 6 * x 12 * x 22
    + x 6 * x 14 * x 20
    - x 6 * x 16 * x 18
    - x 7 * x 10 * x 23
    + x 7 * x 11 * x 22
    - x 7 * x 14 * x 19
    + x 7 * x 15 * x 18
    + x 8 * x 10 * x 21
    - x 8 * x 11 * x 20
    + x 8 * x 12 * x 19
    - x 8 * x 13 * x 18
    - x 9 * x 10 * x 17
    + x 9 * x 11 * x 16
    - x 9 * x 12 * x 15
    + x 9 * x 13 * x 14


theorem source_nilpotent : ∀ (s : Bool) (i : Fin 6) (r : Fin 27),
    (source s i r).bind (source s i) = none := by decide +kernel

theorem operator_square (s : Bool) (i : Fin 6) (x : Fin 27 → R) :
    operator s i (operator s i x) = 0 := by
  funext r
  have h := source_nilpotent s i r
  cases hs : source s i r with
  | none => simp [operator, hs]
  | some j =>
    have hj : source s i j = none := by simpa [hs] using h
    simp [operator, hs, hj]

theorem curve_add (s : Bool) (i : Fin 6) (t v : R) (x : Fin 27 → R) :
    curve s i (t + v) x = curve s i t (curve s i v x) := by
  simp only [curve, map_add, map_smul, operator_square, smul_zero, add_zero,
    add_smul]
  abel

@[simp] theorem curve_zero (s : Bool) (i : Fin 6) (x : Fin 27 → R) :
    curve s i 0 x = x := by simp [curve]

/-- The actual invertible transvection, with inverse parameter `-t`. -/
def curveEquiv (s : Bool) (i : Fin 6) (t : R) : Equiv.Perm (Fin 27 → R) where
  toFun := curve s i t
  invFun := curve s i (-t)
  left_inv x := by rw [← curve_add]; simp
  right_inv x := by rw [← curve_add]; simp

@[simp] theorem curveEquiv_apply (s : Bool) (i : Fin 6) (t : R) (x : Fin 27 → R) :
    curveEquiv s i t x = curve s i t x := rfl

/- The six node certificates are emitted by `source/derive.py --lean-proof`.
Each declaration checks both signs. Explicit substitutions avoid simplifier
processing of the large row table, and the independent node boundaries keep
elaboration within the default heartbeat budget. -/
private theorem cubic_curve_node0 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 0 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * 0) * (x 9 + t * x 18) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * x 26)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * x 14) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * x 26)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * x 12) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * x 26)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * x 11) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * x 26)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * 0) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * x 10) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * x 10) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * x 10) * (x 12 + t * 0) * (x 23 + t * 0)
      - (x 4 + t * x 10) * (x 14 + t * 0) * (x 21 + t * 0)
      + (x 4 + t * x 10) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * x 26)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * x 11) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * x 11) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * x 11) * (x 14 + t * 0) * (x 20 + t * 0)
      - (x 6 + t * x 11) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * x 12) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * x 12) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * x 12) * (x 14 + t * 0) * (x 19 + t * 0)
      + (x 7 + t * x 12) * (x 15 + t * 0) * (x 18 + t * 0)
      + (x 8 + t * x 14) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * x 14) * (x 11 + t * 0) * (x 20 + t * 0)
      + (x 8 + t * x 14) * (x 12 + t * 0) * (x 19 + t * 0)
      - (x 8 + t * x 14) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * x 18) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * x 18) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * x 18) * (x 12 + t * 0) * (x 15 + t * 0)
      + (x 9 + t * x 18) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * x 25)
      - (x 0 + t * 0) * (x 18 + t * x 9) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * x 25)
      + (x 1 + t * 0) * (x 14 + t * x 8) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * x 25)
      - (x 2 + t * 0) * (x 12 + t * x 7) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * 0) * (x 26 + t * x 25)
      + (x 3 + t * 0) * (x 11 + t * x 6) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * 0) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * x 25)
      - (x 4 + t * 0) * (x 11 + t * x 6) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * x 7) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * x 8) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * x 9)
      - (x 5 + t * 0) * (x 10 + t * x 4) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * x 4) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * x 7) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * x 8) * (x 20 + t * 0)
      - (x 6 + t * 0) * (x 16 + t * 0) * (x 18 + t * x 9)
      - (x 7 + t * 0) * (x 10 + t * x 4) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * x 6) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * x 8) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * 0) * (x 18 + t * x 9)
      + (x 8 + t * 0) * (x 10 + t * x 4) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * x 6) * (x 20 + t * 0)
      + (x 8 + t * 0) * (x 12 + t * x 7) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * x 9)
      - (x 9 + t * 0) * (x 10 + t * x 4) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * x 6) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * x 7) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * x 8) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

private theorem cubic_curve_node1 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 1 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * x 19) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * x 25)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * x 15) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * x 25)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * x 13) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * x 25)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * x 4) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * x 4) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * x 4) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * x 4) * (x 15 + t * 0) * (x 21 + t * 0)
      - (x 3 + t * x 4) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * x 6) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * x 25)
      + (x 4 + t * 0) * (x 12 + t * x 13) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * x 15) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * x 19)
      - (x 5 + t * x 6) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * x 6) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * x 6) * (x 15 + t * 0) * (x 20 + t * 0)
      + (x 5 + t * x 6) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * x 25)
      - (x 6 + t * 0) * (x 12 + t * x 13) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * x 15) * (x 20 + t * 0)
      - (x 6 + t * 0) * (x 16 + t * 0) * (x 18 + t * x 19)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * x 15) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * 0) * (x 18 + t * x 19)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * 0)
      + (x 8 + t * 0) * (x 12 + t * x 13) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * x 19)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * x 13) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * x 15) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * x 24)
      + (x 0 + t * 0) * (x 19 + t * x 18) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * x 24)
      - (x 1 + t * 0) * (x 15 + t * x 14) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * x 24)
      + (x 2 + t * 0) * (x 13 + t * x 12) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * x 5) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * x 24)
      - (x 3 + t * 0) * (x 13 + t * x 12) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * x 14) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * x 18)
      + (x 4 + t * x 3) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * x 3) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * x 3) * (x 12 + t * 0) * (x 23 + t * 0)
      - (x 4 + t * x 3) * (x 14 + t * 0) * (x 21 + t * 0)
      + (x 4 + t * x 3) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * x 24)
      + (x 5 + t * 0) * (x 13 + t * x 12) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * x 14) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * x 18)
      + (x 6 + t * x 5) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * x 5) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * x 5) * (x 14 + t * 0) * (x 20 + t * 0)
      - (x 6 + t * x 5) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * 0) * (x 19 + t * x 18)
      + (x 7 + t * 0) * (x 15 + t * x 14) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * 0)
      + (x 8 + t * 0) * (x 12 + t * 0) * (x 19 + t * x 18)
      - (x 8 + t * 0) * (x 13 + t * x 12) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * x 14)
      + (x 9 + t * 0) * (x 13 + t * x 12) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

private theorem cubic_curve_node2 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 2 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * x 20) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * x 24)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * x 16) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * x 24)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * x 3) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * x 3) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * x 3) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * x 3) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * x 3) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * x 7) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * x 12) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * x 24)
      + (x 3 + t * 0) * (x 15 + t * x 16) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * x 20)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * x 12) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * 0) * (x 23 + t * x 24)
      - (x 4 + t * 0) * (x 14 + t * 0) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * x 16) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * x 20)
      + (x 6 + t * x 7) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * x 7) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * x 7) * (x 14 + t * 0) * (x 20 + t * 0)
      - (x 6 + t * x 7) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * x 24)
      + (x 7 + t * 0) * (x 11 + t * x 12) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * 0) * (x 19 + t * x 20)
      + (x 7 + t * 0) * (x 15 + t * x 16) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * x 12) * (x 20 + t * 0)
      + (x 8 + t * 0) * (x 12 + t * 0) * (x 19 + t * x 20)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * x 12) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * x 16)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * x 23)
      - (x 0 + t * 0) * (x 20 + t * x 19) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * x 23)
      + (x 1 + t * 0) * (x 16 + t * x 15) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * x 6) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * x 11) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * x 23)
      - (x 2 + t * 0) * (x 16 + t * x 15) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * x 19)
      - (x 3 + t * x 2) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * x 2) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * x 2) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * x 2) * (x 15 + t * 0) * (x 21 + t * 0)
      - (x 3 + t * x 2) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * x 23)
      + (x 4 + t * 0) * (x 12 + t * x 11) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * 0) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * x 19)
      + (x 5 + t * 0) * (x 16 + t * x 15) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * x 23)
      - (x 6 + t * 0) * (x 12 + t * x 11) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * 0) * (x 20 + t * x 19)
      - (x 6 + t * 0) * (x 16 + t * x 15) * (x 18 + t * 0)
      - (x 7 + t * x 6) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * x 6) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * x 6) * (x 14 + t * 0) * (x 19 + t * 0)
      + (x 7 + t * x 6) * (x 15 + t * 0) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * x 19)
      + (x 8 + t * 0) * (x 12 + t * x 11) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * x 15)
      - (x 9 + t * 0) * (x 12 + t * x 11) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

private theorem cubic_curve_node3 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 3 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * x 21) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * x 23)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * x 17) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * x 23)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * x 17) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * x 21)
      - (x 3 + t * x 5) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * x 5) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * x 5) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * x 5) * (x 15 + t * 0) * (x 21 + t * 0)
      - (x 3 + t * x 5) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * x 6) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * x 6) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * x 6) * (x 12 + t * 0) * (x 23 + t * 0)
      - (x 4 + t * x 6) * (x 14 + t * 0) * (x 21 + t * 0)
      + (x 4 + t * x 6) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * x 11) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * x 23)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * x 21)
      + (x 5 + t * 0) * (x 16 + t * x 17) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * x 11) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * 0) * (x 22 + t * x 23)
      + (x 6 + t * 0) * (x 14 + t * 0) * (x 20 + t * x 21)
      - (x 6 + t * 0) * (x 16 + t * x 17) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * x 11) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * x 23)
      - (x 7 + t * 0) * (x 14 + t * 0) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * 0) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * x 11) * (x 21 + t * 0)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * x 21)
      + (x 8 + t * 0) * (x 12 + t * 0) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * x 11) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * x 17)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * x 22)
      + (x 0 + t * 0) * (x 21 + t * x 20) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * x 22)
      - (x 1 + t * 0) * (x 17 + t * x 16) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * x 20)
      + (x 2 + t * 0) * (x 17 + t * x 16) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * x 4) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * x 10) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * x 22)
      + (x 3 + t * 0) * (x 15 + t * 0) * (x 21 + t * x 20)
      - (x 3 + t * 0) * (x 17 + t * x 16) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * x 3) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * x 10) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * 0) * (x 23 + t * x 22)
      - (x 4 + t * 0) * (x 14 + t * 0) * (x 21 + t * x 20)
      + (x 4 + t * 0) * (x 17 + t * x 16) * (x 18 + t * 0)
      - (x 5 + t * x 3) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * x 3) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * x 3) * (x 15 + t * 0) * (x 20 + t * 0)
      + (x 5 + t * x 3) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * x 4) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * x 4) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * x 4) * (x 14 + t * 0) * (x 20 + t * 0)
      - (x 6 + t * x 4) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * x 22)
      + (x 7 + t * 0) * (x 11 + t * x 10) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * 0) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * 0) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * x 20)
      - (x 8 + t * 0) * (x 11 + t * x 10) * (x 20 + t * 0)
      + (x 8 + t * 0) * (x 12 + t * 0) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * x 16)
      + (x 9 + t * 0) * (x 11 + t * x 10) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

private theorem cubic_curve_node4 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 4 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * x 22) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * x 23) * (x 22 + t * 0)
      - (x 1 + t * x 2) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * x 2) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * x 2) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * x 2) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * x 2) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * x 8) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * x 14) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * x 15) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * x 23)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * x 22)
      - (x 3 + t * 0) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * x 15) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * 0) * (x 21 + t * x 23)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * x 14) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * 0) * (x 21 + t * x 23)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * x 15) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * x 22)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * x 14) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * 0) * (x 20 + t * x 22)
      - (x 6 + t * 0) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * x 8) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * x 8) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * x 8) * (x 14 + t * 0) * (x 19 + t * 0)
      + (x 7 + t * x 8) * (x 15 + t * 0) * (x 18 + t * 0)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * x 23)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * x 22)
      + (x 8 + t * 0) * (x 12 + t * x 14) * (x 19 + t * 0)
      - (x 8 + t * 0) * (x 13 + t * x 15) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * x 14) * (x 15 + t * 0)
      + (x 9 + t * 0) * (x 13 + t * x 15) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * 0) * (x 23 + t * x 21)
      + (x 0 + t * 0) * (x 21 + t * 0) * (x 22 + t * x 20)
      - (x 1 + t * 0) * (x 8 + t * x 7) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * x 12) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * x 13) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * 0) * (x 23 + t * x 21)
      - (x 1 + t * 0) * (x 17 + t * 0) * (x 22 + t * x 20)
      + (x 2 + t * x 1) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * x 1) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * x 1) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * x 1) * (x 16 + t * 0) * (x 21 + t * 0)
      + (x 2 + t * x 1) * (x 17 + t * 0) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * x 21)
      + (x 3 + t * 0) * (x 15 + t * x 13) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * 0) * (x 23 + t * x 21)
      - (x 4 + t * 0) * (x 14 + t * x 12) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * x 20)
      - (x 5 + t * 0) * (x 15 + t * x 13) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * 0) * (x 22 + t * x 20)
      + (x 6 + t * 0) * (x 14 + t * x 12) * (x 20 + t * 0)
      - (x 6 + t * 0) * (x 16 + t * 0) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * x 21)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * x 20)
      - (x 7 + t * 0) * (x 14 + t * x 12) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * x 13) * (x 18 + t * 0)
      + (x 8 + t * x 7) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * x 7) * (x 11 + t * 0) * (x 20 + t * 0)
      + (x 8 + t * x 7) * (x 12 + t * 0) * (x 19 + t * 0)
      - (x 8 + t * x 7) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * x 13)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * x 12) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

private theorem cubic_curve_node5 (s : Bool) (t : R) (x : Fin 27 → R) :
    cubic (curve s 5 t x) = cubic x := by
  cases s
  · change
      (x 0 + t * x 1) * (x 9 + t * 0) * (x 26 + t * 0)
      - (x 0 + t * x 1) * (x 18 + t * 0) * (x 25 + t * 0)
      + (x 0 + t * x 1) * (x 19 + t * 0) * (x 24 + t * 0)
      - (x 0 + t * x 1) * (x 20 + t * 0) * (x 23 + t * 0)
      + (x 0 + t * x 1) * (x 21 + t * 0) * (x 22 + t * 0)
      - (x 1 + t * 0) * (x 8 + t * x 9) * (x 26 + t * 0)
      + (x 1 + t * 0) * (x 14 + t * x 18) * (x 25 + t * 0)
      - (x 1 + t * 0) * (x 15 + t * x 19) * (x 24 + t * 0)
      + (x 1 + t * 0) * (x 16 + t * x 20) * (x 23 + t * 0)
      - (x 1 + t * 0) * (x 17 + t * x 21) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * x 20) * (x 21 + t * 0)
      + (x 2 + t * 0) * (x 17 + t * x 21) * (x 20 + t * 0)
      - (x 3 + t * 0) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * x 19) * (x 21 + t * 0)
      - (x 3 + t * 0) * (x 17 + t * x 21) * (x 19 + t * 0)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * 0) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * x 18) * (x 21 + t * 0)
      + (x 4 + t * 0) * (x 17 + t * x 21) * (x 18 + t * 0)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * x 19) * (x 20 + t * 0)
      + (x 5 + t * 0) * (x 16 + t * x 20) * (x 19 + t * 0)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * x 18) * (x 20 + t * 0)
      - (x 6 + t * 0) * (x 16 + t * x 20) * (x 18 + t * 0)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * x 18) * (x 19 + t * 0)
      + (x 7 + t * 0) * (x 15 + t * x 19) * (x 18 + t * 0)
      + (x 8 + t * x 9) * (x 10 + t * 0) * (x 21 + t * 0)
      - (x 8 + t * x 9) * (x 11 + t * 0) * (x 20 + t * 0)
      + (x 8 + t * x 9) * (x 12 + t * 0) * (x 19 + t * 0)
      - (x 8 + t * x 9) * (x 13 + t * 0) * (x 18 + t * 0)
      - (x 9 + t * 0) * (x 10 + t * 0) * (x 17 + t * x 21)
      + (x 9 + t * 0) * (x 11 + t * 0) * (x 16 + t * x 20)
      - (x 9 + t * 0) * (x 12 + t * 0) * (x 15 + t * x 19)
      + (x 9 + t * 0) * (x 13 + t * 0) * (x 14 + t * x 18) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring
  · change
      (x 0 + t * 0) * (x 9 + t * x 8) * (x 26 + t * 0)
      - (x 0 + t * 0) * (x 18 + t * x 14) * (x 25 + t * 0)
      + (x 0 + t * 0) * (x 19 + t * x 15) * (x 24 + t * 0)
      - (x 0 + t * 0) * (x 20 + t * x 16) * (x 23 + t * 0)
      + (x 0 + t * 0) * (x 21 + t * x 17) * (x 22 + t * 0)
      - (x 1 + t * x 0) * (x 8 + t * 0) * (x 26 + t * 0)
      + (x 1 + t * x 0) * (x 14 + t * 0) * (x 25 + t * 0)
      - (x 1 + t * x 0) * (x 15 + t * 0) * (x 24 + t * 0)
      + (x 1 + t * x 0) * (x 16 + t * 0) * (x 23 + t * 0)
      - (x 1 + t * x 0) * (x 17 + t * 0) * (x 22 + t * 0)
      + (x 2 + t * 0) * (x 7 + t * 0) * (x 26 + t * 0)
      - (x 2 + t * 0) * (x 12 + t * 0) * (x 25 + t * 0)
      + (x 2 + t * 0) * (x 13 + t * 0) * (x 24 + t * 0)
      - (x 2 + t * 0) * (x 16 + t * 0) * (x 21 + t * x 17)
      + (x 2 + t * 0) * (x 17 + t * 0) * (x 20 + t * x 16)
      - (x 3 + t * 0) * (x 6 + t * 0) * (x 26 + t * 0)
      + (x 3 + t * 0) * (x 11 + t * 0) * (x 25 + t * 0)
      - (x 3 + t * 0) * (x 13 + t * 0) * (x 23 + t * 0)
      + (x 3 + t * 0) * (x 15 + t * 0) * (x 21 + t * x 17)
      - (x 3 + t * 0) * (x 17 + t * 0) * (x 19 + t * x 15)
      + (x 4 + t * 0) * (x 5 + t * 0) * (x 26 + t * 0)
      - (x 4 + t * 0) * (x 11 + t * 0) * (x 24 + t * 0)
      + (x 4 + t * 0) * (x 12 + t * 0) * (x 23 + t * 0)
      - (x 4 + t * 0) * (x 14 + t * 0) * (x 21 + t * x 17)
      + (x 4 + t * 0) * (x 17 + t * 0) * (x 18 + t * x 14)
      - (x 5 + t * 0) * (x 10 + t * 0) * (x 25 + t * 0)
      + (x 5 + t * 0) * (x 13 + t * 0) * (x 22 + t * 0)
      - (x 5 + t * 0) * (x 15 + t * 0) * (x 20 + t * x 16)
      + (x 5 + t * 0) * (x 16 + t * 0) * (x 19 + t * x 15)
      + (x 6 + t * 0) * (x 10 + t * 0) * (x 24 + t * 0)
      - (x 6 + t * 0) * (x 12 + t * 0) * (x 22 + t * 0)
      + (x 6 + t * 0) * (x 14 + t * 0) * (x 20 + t * x 16)
      - (x 6 + t * 0) * (x 16 + t * 0) * (x 18 + t * x 14)
      - (x 7 + t * 0) * (x 10 + t * 0) * (x 23 + t * 0)
      + (x 7 + t * 0) * (x 11 + t * 0) * (x 22 + t * 0)
      - (x 7 + t * 0) * (x 14 + t * 0) * (x 19 + t * x 15)
      + (x 7 + t * 0) * (x 15 + t * 0) * (x 18 + t * x 14)
      + (x 8 + t * 0) * (x 10 + t * 0) * (x 21 + t * x 17)
      - (x 8 + t * 0) * (x 11 + t * 0) * (x 20 + t * x 16)
      + (x 8 + t * 0) * (x 12 + t * 0) * (x 19 + t * x 15)
      - (x 8 + t * 0) * (x 13 + t * 0) * (x 18 + t * x 14)
      - (x 9 + t * x 8) * (x 10 + t * 0) * (x 17 + t * 0)
      + (x 9 + t * x 8) * (x 11 + t * 0) * (x 16 + t * 0)
      - (x 9 + t * x 8) * (x 12 + t * 0) * (x 15 + t * 0)
      + (x 9 + t * x 8) * (x 13 + t * 0) * (x 14 + t * 0) =
      x 0 * x 9 * x 26
      - x 0 * x 18 * x 25
      + x 0 * x 19 * x 24
      - x 0 * x 20 * x 23
      + x 0 * x 21 * x 22
      - x 1 * x 8 * x 26
      + x 1 * x 14 * x 25
      - x 1 * x 15 * x 24
      + x 1 * x 16 * x 23
      - x 1 * x 17 * x 22
      + x 2 * x 7 * x 26
      - x 2 * x 12 * x 25
      + x 2 * x 13 * x 24
      - x 2 * x 16 * x 21
      + x 2 * x 17 * x 20
      - x 3 * x 6 * x 26
      + x 3 * x 11 * x 25
      - x 3 * x 13 * x 23
      + x 3 * x 15 * x 21
      - x 3 * x 17 * x 19
      + x 4 * x 5 * x 26
      - x 4 * x 11 * x 24
      + x 4 * x 12 * x 23
      - x 4 * x 14 * x 21
      + x 4 * x 17 * x 18
      - x 5 * x 10 * x 25
      + x 5 * x 13 * x 22
      - x 5 * x 15 * x 20
      + x 5 * x 16 * x 19
      + x 6 * x 10 * x 24
      - x 6 * x 12 * x 22
      + x 6 * x 14 * x 20
      - x 6 * x 16 * x 18
      - x 7 * x 10 * x 23
      + x 7 * x 11 * x 22
      - x 7 * x 14 * x 19
      + x 7 * x 15 * x 18
      + x 8 * x 10 * x 21
      - x 8 * x 11 * x 20
      + x 8 * x 12 * x 19
      - x 8 * x 13 * x 18
      - x 9 * x 10 * x 17
      + x 9 * x 11 * x 16
      - x 9 * x 12 * x 15
      + x 9 * x 13 * x 14
    ring

/-- Direct polynomial identities for all twelve signed generators. No integer is inverted. -/
theorem cubic_curve (s : Bool) (i : Fin 6) (t : R) (x : Fin 27 → R) :
    cubic (curve s i t x) = cubic x := by
  fin_cases i
  · exact cubic_curve_node0 s t x
  · exact cubic_curve_node1 s t x
  · exact cubic_curve_node2 s t x
  · exact cubic_curve_node3 s t x
  · exact cubic_curve_node4 s t x
  · exact cubic_curve_node5 s t x

/-- Literal evaluation of the same signed six-node alphabet on the 27 coordinates. -/
def evaluation : FreeGroup (Bool × Fin 6 × R) →* Equiv.Perm (Fin 27 → R) :=
  FreeGroup.lift fun a => curveEquiv a.1 a.2.1 a.2.2

@[simp] theorem evaluation_of (s : Bool) (i : Fin 6) (t : R) :
    evaluation (FreeGroup.of (s, i, t)) = curveEquiv s i t := FreeGroup.lift_apply_of

/-- The cubic is invariant under evaluated words, including inverse letters. -/
theorem cubic_evaluation (w : FreeGroup (Bool × Fin 6 × R)) (x : Fin 27 → R) :
    cubic (evaluation w x) = cubic x := by
  induction w using FreeGroup.induction_on generalizing x with
  | C1 => simp
  | of a => exact cubic_curve a.1 a.2.1 a.2.2 x
  | inv_of a ih =>
    have h := ih (evaluation (FreeGroup.of a)⁻¹ x)
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm
  | mul a b ha hb =>
    rw [map_mul, Equiv.Perm.mul_apply, ha, hb]

/-- Homogeneity is an integral polynomial identity, so also holds in characteristic three. -/
theorem cubic_smul (t : R) (x : Fin 27 → R) :
    cubic (t • x) = t ^ 3 * cubic x := by
  simp only [cubic, Pi.smul_apply, smul_eq_mul]
  ring

/-- This vector evaluates to one, exhibiting the normalization over every coefficient ring. -/
def witness : Fin 27 → R := fun i => if i = 0 ∨ i = 9 ∨ i = 26 then 1 else 0

@[simp] theorem cubic_witness : cubic (witness : Fin 27 → R) = 1 := by
  norm_num [cubic, witness, Fin.ext_iff]

/-- A scalar in the word image satisfies the cubic equation, including in characteristic three. -/
theorem cube_of_evaluation_scalar (w : FreeGroup (Bool × Fin 6 × R)) (t : R)
    (h : ∀ x, evaluation w x = t • x) : t ^ 3 = 1 := by
  have he := cubic_evaluation w (witness : Fin 27 → R)
  rw [h, cubic_smul, cubic_witness, mul_one] at he
  exact he

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.CubicModel
