module

public import Mathlib.Tactic.Linter.FlexibleLinter
public import Mathlib.Tactic.Linter.Header

/-!
# Elementary lookup arithmetic for the degree-1792 low products

Packed tables contain all sixteen XOR sums of four right-hand rows. Each
left-hand row is supplied in base 2^32, so numerical certificates avoid
repeated division of the full 1792-bit integer. Soundness, table validation,
and full input comparisons are proved separately in Arithmetic and Tables.

Source: ATLAS M24G1-P1 word 2; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts.Arithmetic

def tableEntry (t i : Nat) : Nat := (t >>> (1792 * i)) &&& (nat_lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

def tableRow : Nat → List Nat → Nat
  | 0, _ => 0
  | _, [] => 0
  | a + 1, t :: ts => tableEntry t ((a + 1) % 16) ^^^ tableRow ((a + 1) / 16) ts

def packMasks : List Nat → Nat
  | [] => 0
  | a :: as => a % 4294967296 + 4294967296 * packMasks as

def masksRow : List Nat → List (List Nat) → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, ts :: tss => tableRow (a % 4294967296) ts ^^^ masksRow as tss

def masksCheck : List (List Nat) → List (List Nat) → List Nat → Bool
  | [], _, [] => true
  | a :: as, bs, c :: cs => (masksRow a bs == c) && masksCheck as bs cs
  | _, _, _ => false

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.LowProducts.Arithmetic
