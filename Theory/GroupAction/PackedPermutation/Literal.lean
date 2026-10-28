module
public import Mathlib.Data.Nat.Bitwise
public meta import Lean.Elab.ElabRules
/-!
# Large packed natural-number literals

The data-only elaborator reads hexadecimal digits in small chunks and combines
those chunks in a balanced tree. It emits an ordinary `Nat` literal, which the
kernel treats exactly like a built-in numeral. It constructs no proofs and
asserts no relation between the literal and any permutation.

This avoids the large-token parsing and overloaded-numeral elaboration costs
observed while checking switching networks for the ATLAS Fi24 permutation
carrier. All equalities involving the emitted data are checked separately by
the kernel.
-/

public meta section
namespace Theory.GroupAction.PackedPermutation
open Lean Elab Term
/-- Data-only parser: emit an ordinary natural-number literal. -/
elab "packed_nat% " s:str : term => do
  let bytes := s.getString.toUTF8
  let mut pieces : Array (Nat × Nat) := #[]
  let mut n := 0
  let mut len := 0
  for c in bytes do
    let x := c.toNat
    let digit := if x < 58 then x - 48 else x - 87
    unless (48 ≤ x && x ≤ 57) || (97 ≤ x && x ≤ 102) do
      throwError "invalid hexadecimal data"
    n := n * 16 + digit
    len := len + 4
    if len == 256 then
      pieces := pieces.push (n, len)
      n := 0
      len := 0
  if len != 0 then pieces := pieces.push (n, len)
  while pieces.size > 1 do
    let mut next : Array (Nat × Nat) := #[]
    for i in [: (pieces.size + 1) / 2] do
      let a := pieces[2*i]!
      if 2*i+1 < pieces.size then
        let b := pieces[2*i+1]!
        next := next.push ((a.1 <<< b.2) ||| b.1, a.2+b.2)
      else next := next.push a
    pieces := next
  return mkNatLit (pieces[0]?.getD (0,0)).1
end Theory.GroupAction.PackedPermutation
