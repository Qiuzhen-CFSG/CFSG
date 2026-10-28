module

public import Mathlib.Tactic.Linter.FlexibleLinter
public import Mathlib.Tactic.Linter.Header

/-!
# Elementary computations for the degree-1792 high products

Only natural numbers and lists are needed for the certificate reductions.
The two linter imports register the options used by this repository's Lake
configuration. Matrix imports and all soundness proofs live in `Checker`;
keeping them out of numerical leaves reduces repeated compilation memory.
The exposed bodies are required for kernel reduction of the certificates.

Source: ATLAS M24G1-P1, word 2; see `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts

def small : Nat → List Nat → Nat
  | _, [] => 0
  | a, b :: bs => Nat.xor ((a % 2) * b) (small (a / 2) bs)

def packMasks : List Nat → Nat
  | [] => 0
  | a :: as => a % 65536 + 65536 * packMasks as

def masksRow : List Nat → List (List Nat) → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => small (a % 65536) b ^^^ masksRow as bs

def masksCheck : List (List Nat) → List (List Nat) → List Nat → Bool
  | [], _, [] => true
  | a :: as, bs, c :: cs => (masksRow a bs == c) && masksCheck as bs cs
  | _, _, _ => false

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23.HighProducts
