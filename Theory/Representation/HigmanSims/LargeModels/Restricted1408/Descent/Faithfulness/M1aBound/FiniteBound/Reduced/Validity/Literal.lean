module

public import Mathlib.Tactic.Linter.FlexibleLinter
public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder

/-!
# Syntax for literal certificate words

This elaborator expands an integer into a literal list of natural-number
letters. It creates data only. All subsequent group deductions and word
identities are checked by the kernel, independently of this expansion.
-/

public meta section
open Lean Elab Term Meta

syntax (name := hsWordLiteral) "hs_word% " num : term

@[term_elab hsWordLiteral] def elabHSWordLiteral : TermElab := fun stx _ => do
  let some n := stx[1].isNatLit? | throwError "expected a natural-number word code"
  let mut code := n
  let mut letters : Array Expr := #[]
  while code != 0 do
    let digit := code % 256
    if digit == 0 || digit > 202 then
      throwError "invalid HS word digit"
    let x := digit - 1
    let sign := if x % 2 == 0 then Lean.mkConst ``Bool.true else Lean.mkConst ``Bool.false
    letters := letters.push (mkAppN (Lean.mkConst ``Prod.mk [.zero, .zero])
      #[Lean.mkConst ``Nat, Lean.mkConst ``Bool, mkNatLit (x / 2), sign])
    code := code / 256
  mkListLit (mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) (Lean.mkConst ``Nat) (Lean.mkConst ``Bool))
    letters.toList
