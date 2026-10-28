module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Bridges.V
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.Products.VSquare.Arithmetic

/-!
# Checked row selection for the fixed V products

A monomial left row selects a single row of V. The input bridge identifies its
widened entry, and compression recovers the binary row; all original V rows
are checked to fit in 1792 bits. Every use verifies the proposed index and
power-of-two equality. Other rows use the established carry-free checker.

The certificate pairs retain every original left row: their first projection
is separately checked before the numerical results are converted to the exact
blocked row equations used by `product_chunks`.

Source: ATLAS M24G1-P1; see `../../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks.Monomial
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

private theorem compress_expand (n a : Nat) : compress n (expand n a) = a % 2 ^ n := by
  induction n generalizing a with
  | zero => simp only [compress, pow_zero, Nat.mod_one]
  | succ n ih =>
    have hm : a % 2 < 2048 := lt_trans (Nat.mod_lt a (by decide)) (by decide)
    have hp : (a % 2 + 2048 * expand n (a / 2)) % 2 = a % 2 := by omega
    have hq : (a % 2 + 2048 * expand n (a / 2)) / 2048 = expand n (a / 2) := by
      simp [Nat.add_mul_div_left, Nat.div_eq_of_lt hm]
    rw [expand, compress, hp, hq, ih, pow_succ']
    calc
      a % 2 + 2 * (a / 2 % 2 ^ n) =
          (a % (2 * 2 ^ n)) % 2 + 2 * ((a % (2 * 2 ^ n)) / 2) := by
        rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self]
      _ = _ := Nat.mod_add_div _ _

private theorem accum_two_pow (i : Nat) (xs : List Nat) : accum (2 ^ i) xs = xs[i]! := by
  induction xs generalizing i with
  | nil => simp [accum]
  | cons x xs ih =>
    cases i with
    | zero => simp [accum, VChecks.accum_zero]
    | succ i => simpa [pow_succ', accum] using ih i

set_option maxRecDepth 8192 in
private theorem row_bounds : ∀ a ∈ Data.vRows, a < 2 ^ 1792 := by decide +kernel

private theorem row_lengths : ∀ b ∈ Data.vBlocks, b.length = 32 := by decide +kernel

private theorem monomial (i : Nat) (hi : i < 1792) :
    compressBlocks 32 56 (accumChunks (2 ^ i) Inputs.vWide) =
      getRow 32 Data.vBlocks i := by
  have hir : i < Data.vRows.length := by simpa only [Data.vRows_length] using hi
  have hw : Inputs.vWide.flatten[i]! = expand 1792 Data.vRows[i]! := by
    rw [v_wide]
    simp [hir, expandBlocks_eq]
  have hb : Data.vRows[i]! < 2 ^ 1792 := by
    simpa only [getElem!_pos, hir] using row_bounds Data.vRows[i] (List.getElem_mem hir)
  rw [compressBlocks_eq, accumChunks_eq, accum_two_pow, hw, compress_expand,
    Nat.mod_eq_of_lt hb, getRow_eq 32 (by decide) Data.vBlocks row_lengths]
  rfl

def row (x : Nat × Nat) : Nat :=
  if x.1 = 2 ^ x.2 ∧ x.2 < 1792 then getRow 32 Data.vBlocks x.2
  else VChecks.fastRow x.1

private theorem row_eq (x : Nat × Nat) :
    row x = compressBlocks 32 56 (accumChunks x.1 Inputs.vWide) := by
  unfold row
  split
  · next h => simpa only [← h.1] using (monomial x.2 h.2).symm
  · exact VChecks.fastRow_eq x.1

theorem rows (pairs : List (Nat × Nat)) (xs ys : List Nat)
    (hx : pairs.map Prod.fst = xs) (h : pairs.map row = ys) :
    xs.map (fun a => compressBlocks 32 56 (accumChunks a Inputs.vWide)) = ys := by
  let f : Nat → Nat := fun a => compressBlocks 32 56 (accumChunks a Inputs.vWide)
  have hm (ps : List (Nat × Nat)) : (ps.map Prod.fst).map f = ps.map row := by
    induction ps with
    | nil => rfl
    | cons x ps ih =>
      exact congrArg₂ List.cons (row_eq x).symm ih
  exact (congrArg (List.map f) hx.symm).trans ((hm pairs).trans h)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks.Monomial
