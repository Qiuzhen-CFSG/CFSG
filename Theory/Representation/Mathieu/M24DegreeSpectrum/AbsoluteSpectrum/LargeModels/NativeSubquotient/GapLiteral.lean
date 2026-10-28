module

public meta import Lean.Elab.ElabRules
public import Mathlib.Tactic.Linter.FlexibleLinter

/-!
# Literal gap-list data for the native matrix certificates

The elaborator expands comma-separated naturals directly into ordinary
`List Nat` constructor terms, with an explicit tail. This avoids repeated
elaboration of overloaded numerals in the large saved certificates. It
constructs data only, never proofs. Both mask reconstruction and all products
are still checked by the kernel in the consuming certificate modules.

Pattern adapted from this repository's `PointBound/Reduction/WordLiteral`
(Apache-2.0); consumers: the native 1242 and 1792 matrix certificates.
-/

public meta section
open Lean Elab Term

/-- Expand natural-number data and an explicit tail to a literal list. -/
elab "native_gaps% " s:str " [" tail:term "]" : term => do
  let type := Lean.mkConst ``Nat
  let mut result ← elabTerm tail (some (mkApp (mkConst ``List [Level.zero]) type))
  if s.getString.isEmpty then return result
  for token in (s.getString.splitOn ",").reverse do
    let some n := token.toNat? | throwError "invalid natural-number gap: {token}"
    result := mkApp3 (mkConst ``List.cons [Level.zero]) type (mkNatLit n) result
  return result
end
