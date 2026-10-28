module

public import Mathlib.Tactic.Linter.FlexibleLinter
public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder

/-!
# Ordinary proof terms for elementary certificate steps

This elaborator expands instruction indices into applications of the proved
calculus lemmas and `Eq.refl`. Lean's kernel checks every resulting application,
including all literal word identities. No evaluation oracle is used.
-/

public meta section
open Lean Elab Term Meta

syntax (name := hsDeduction) "hs_deduction% " num num num num num num num num : term

@[term_elab hsDeduction] def elabHSDeduction : TermElab := fun stx _ => do
  let mut args : Array Nat := #[]
  for i in [1:9] do
    let some n := stx[i].isNatLit? | throwError "expected a certificate index"
    args := args.push n
  let n := args[0]!
  let kind := args[1]!
  let p := args[2]!
  let q := args[3]!
  let ns := `Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.ValidityCertificate
  let word (k : Nat) := Lean.mkConst (ns.str s!"w{k}")
  let fact (k : Nat) := Lean.mkConst (ns.str s!"fact{k}")
  let lemma (s : String) := Lean.mkConst (ns.str s)
  if kind == 0 then
    return lemma "valid_empty"
  if kind == 1 then
    return mkAppN (lemma "valid_source")
      #[mkNatLit p, mkNatLit args[6]!, word n, ← mkEqRefl (word n)]
  if kind != 2 && kind != 3 then throwError "unknown certificate instruction"
  if p >= n || q >= n then throwError "certificate dependency is not earlier"
  let (w, v) := if kind == 2 then (word p, word n) else (word n, word p)
  let positive := Lean.mkConst (if args[7]! == 1 then ``Bool.true else ``Bool.false)
  return mkAppN (lemma (if kind == 2 then "valid_forward" else "valid_backward"))
    #[w, word q, v, mkNatLit args[4]!, mkNatLit args[5]!, mkNatLit args[6]!,
      positive, fact p, fact q, ← mkEqRefl v]
