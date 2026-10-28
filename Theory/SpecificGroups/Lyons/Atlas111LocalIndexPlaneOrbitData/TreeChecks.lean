module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.MaskedChecks

/-!
# Lookup and fold checks for packed Lyons data

Literal data can be stored in a binary tree with natural-number cut points.
Balanced trees give shallow lookup, while a fold checks each leaf once without
repeating lookups or introducing a large finite-quantifier loop. A successful
fold certifies every lookup, independently of the tree's balance, cut points,
or the producer's choices. Repeated padding leaves are therefore harmless for
shape checks. Distinctness still requires its separate exact sorting proof.

This is the tree version of the interval splitting interface in `MaskedChecks`;
it is intended for the packed records from `Atlas111PlaneOrbitSource/GenerateOrbit.py`.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitData

/-- A data tree whose branch cut points refer to the original natural index. -/
inductive LookupTree (α : Type*) where
  | leaf (value : α)
  | branch (cut : ℕ) (left right : LookupTree α)

namespace LookupTree
variable {α : Type*}

/-- Total lookup; balancing is an optimization, not a soundness assumption. -/
def get : LookupTree α → ℕ → α
  | .leaf value, _ => value
  | .branch cut left right, i => if i < cut then left.get i else right.get i

/-- Check all leaves once. This remains separate from indexed lookup. -/
def check (f : α → Bool) : LookupTree α → Bool
  | .leaf value => f value
  | .branch _ left right => check f left && check f right

/-- Every value returned by lookup passes a successful leaf check. -/
theorem check_get (f : α → Bool) (tree : LookupTree α)
    (h : tree.check f = true) (i : ℕ) : f (tree.get i) = true := by
  induction tree with
  | leaf value => exact h
  | branch cut left right ihl ihr =>
    have hp := (Bool.and_eq_true _ _).mp h
    change f (if i < cut then left.get i else right.get i) = true
    split_ifs
    · exact ihl hp.1
    · exact ihr hp.2

/-- Fold checks feed the interval-based reduced-basis and separation interfaces. -/
theorem maskedCheckedOn_of_check (tree : LookupTree α)
    (rows : α → PackedRows) (pattern : α → MaskPattern)
    (h : tree.check (fun a => checkMaskedNode (rows a) (pattern a)) = true)
    (lo hi : ℕ) :
    MaskedCheckedOn lo hi (fun i => rows (tree.get i)) (fun i => pattern (tree.get i)) := by
  intro i _ _
  exact tree.check_get _ h i

end LookupTree
end Lyons.OrderCertificate.PlaneOrbitData
