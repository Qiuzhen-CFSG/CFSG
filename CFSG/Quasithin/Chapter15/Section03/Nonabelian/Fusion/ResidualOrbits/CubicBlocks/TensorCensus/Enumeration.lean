module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Checked enumeration of binary block coordinates

Six bits encode the two rows of a 2 by 3 binary array, in row-major order,
with the first coordinate as the least significant bit. We list all six
binary determinant-one frames and enumerate their left/right actions,
with the four possible translations. Every table assertion below is checked
by the kernel. The parent module identifies these formulas with the published
block action and transports the calculation to its orbit relation.

Source: Aschbacher–Smith, 15.3.61(2), printed pp.1150–1151.
-/

@[expose] public section
open Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.TensorEnumeration

abbrev Point := Multiplicative (Fin 2 → Fin 3 → ZMod 2)
abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 2)

def frameMatrix : Fin 6 → Mat :=
  ![!![1,0;0,1], !![0,1;1,0], !![1,1;0,1],
    !![1,0;1,1], !![0,1;1,1], !![1,1;1,0]]

theorem frame_det : ∀ i, (frameMatrix i).det = 1 := by decide +kernel

theorem frames_exhaust : ∀ m : Mat, m.det = 1 → ∃ i, frameMatrix i = m := by
  decide +kernel

def shift (i : Fin 4) : Fin 2 → ZMod 2 := ![(i.val : ZMod 2), (i.val / 2 : ℕ)]

theorem shifts_exhaust : ∀ t : Fin 2 → ZMod 2, ∃ i, shift i = t := by decide +kernel

def encode (x : Point) : ℕ :=
  (x.toAdd 0 0).val + 2 * (x.toAdd 0 1).val + 4 * (x.toAdd 0 2).val +
  8 * (x.toAdd 1 0).val + 16 * (x.toAdd 1 1).val + 32 * (x.toAdd 1 2).val

def decode (n : ℕ) : Point := Multiplicative.ofAdd
  ![![(n : ZMod 2), (n / 2 : ℕ), (n / 4 : ℕ)],
    ![(n / 8 : ℕ), (n / 16 : ℕ), (n / 32 : ℕ)]]

theorem decode_encode : ∀ x : Point, decode (encode x) = x := by decide +kernel

theorem encode_decode : ∀ i : Fin 64, encode (decode i.val) = i.val := by decide +kernel

theorem encode_lt : ∀ x : Point, encode x < 64 := by decide +kernel

/-- The literal matrix formula, evaluated on a decoded coordinate word. -/
def step (l r : Fin 6) (t : Fin 4) (n : ℕ) : ℕ :=
  let x := decode n
  let a := fun i => x.toAdd i 0
  let C : Mat := fun i j => x.toAdd i j.succ
  encode (Multiplicative.ofAdd fun i => Fin.cons
    ((frameMatrix l *ᵥ a) i)
    (fun j => (frameMatrix l * C * (frameMatrix r).transpose) i j +
      (frameMatrix l *ᵥ a) i * shift t j))

/-- The inside orbit needs no translations. -/
def linearOrbit (n : ℕ) : Finset ℕ :=
  Finset.univ.image fun p : Fin 6 × Fin 6 => step p.1 p.2 0 n

def affineOrbit (n : ℕ) : Finset ℕ :=
  Finset.univ.image fun p : Fin 6 × Fin 6 × Fin 4 => step p.1 p.2.1 p.2.2 n

def singularCodes : Finset ℕ := {2, 4, 6, 16, 18, 32, 36, 48, 54}
def nonsingularCodes : Finset ℕ := {20, 22, 34, 38, 50, 52}
def outsideOneCodes : Finset ℕ := {1, 3, 5, 7, 8, 9, 24, 27, 40, 45, 56, 63}
def outsideTwoCodes : Finset ℕ :=
  {10, 11, 12, 13, 14, 15, 17, 19, 21, 23, 25, 26, 28, 29, 30, 31,
   33, 35, 37, 39, 41, 42, 43, 44, 46, 47, 49, 51, 53, 55, 57, 58, 59, 60, 61, 62}
def insideCodes : Finset ℕ := {0} ∪ singularCodes ∪ nonsingularCodes

theorem singular_spec : ∀ x : Point,
    ((fun i => x.toAdd i 0) = 0 ∧ x ≠ 1 ∧
      Matrix.det (fun i j : Fin 2 => x.toAdd i j.succ) = 0) ↔
      encode x ∈ singularCodes := by decide +kernel

theorem nonsingular_spec : ∀ x : Point,
    ((fun i => x.toAdd i 0) = 0 ∧
      Matrix.det (fun i j : Fin 2 => x.toAdd i j.succ) ≠ 0) ↔
      encode x ∈ nonsingularCodes := by decide +kernel

theorem inside_spec : ∀ x : Point,
    (fun i => x.toAdd i 0) = 0 ↔ encode x ∈ insideCodes := by decide +kernel

theorem singular_orbit : ∀ n ∈ singularCodes, linearOrbit n = singularCodes := by
  decide +kernel

theorem nonsingular_orbit : ∀ n ∈ nonsingularCodes, linearOrbit n = nonsingularCodes := by
  decide +kernel

theorem outsideOne_orbit : affineOrbit 1 = outsideOneCodes := by decide +kernel

theorem outsideTwo_orbit : affineOrbit 17 = outsideTwoCodes := by decide +kernel

theorem code_bounds :
    (∀ n ∈ singularCodes, n < 64) ∧ (∀ n ∈ nonsingularCodes, n < 64) ∧
    (∀ n ∈ outsideOneCodes, n < 64) ∧ (∀ n ∈ outsideTwoCodes, n < 64) := by
  decide +kernel

theorem code_cards : singularCodes.card = 9 ∧ nonsingularCodes.card = 6 ∧
    outsideOneCodes.card = 12 ∧ outsideTwoCodes.card = 36 := by decide +kernel

theorem cover : ∀ n : Fin 64, n ≠ 0 → n.val ∈ singularCodes ∨
    n.val ∈ nonsingularCodes ∨ n.val ∈ outsideOneCodes ∨ n.val ∈ outsideTwoCodes := by
  decide +kernel

theorem singular_products : ∀ n ∈ insideCodes,
    ∃ a ∈ singularCodes, ∃ b ∈ singularCodes, decode n = decode a * decode b := by
  decide +kernel

theorem nonsingular_products : ∀ n ∈ insideCodes,
    ∃ a ∈ nonsingularCodes, ∃ b ∈ nonsingularCodes, decode n = decode a * decode b := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.TensorEnumeration
