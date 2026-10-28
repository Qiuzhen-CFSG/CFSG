module

public meta import Lean.Elab.ElabRules
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Literal word syntax for the Tietze certificate

Adapted from the repository’s Held M₁ `TietzeTransfer/WordLiteral.lean`
(Apache-2.0), with zero-based generator indices.

The elaborator expands signed decimal letters into ordinary kernel terms of
`List (Nat × Bool)`. It avoids repeatedly elaborating overloaded numerals and
pair notation in the large tables. It constructs data only, never a proof;
the initial-word checks and the equality replay still run in the Lean kernel.
-/

public meta section
open Lean Elab Term

/-- Expand signed decimal letters into an ordinary literal list of pairs.
Positive k denotes generator k-1; negative k denotes its inverse.
This elaborator constructs syntax data only; it supplies no equality proofs. -/
elab "point_word% " s:str : term => do
  let letter := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``Bool)
  let mut word := mkApp (mkConst ``List.nil [Level.zero]) letter
  if s.getString.isEmpty then return word
  for token in (s.getString.splitOn ",").reverse do
    let some a := token.toInt? | throwError "invalid signed letter: {token}"
    if a == 0 then throwError "zero is not a letter"
    let value := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
      (mkConst ``Nat) (mkConst ``Bool) (mkNatLit (a.natAbs - 1))
      (mkConst (if a > 0 then ``Bool.true else ``Bool.false))
    word := mkApp3 (mkConst ``List.cons [Level.zero]) letter value word
  return word

end
