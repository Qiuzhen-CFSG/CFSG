module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
/-!
# Balanced access to the fixed coset tables

The existing arrays pack 128 entries per natural-number block. A balanced tree
reads those same blocks by the bits of their index. Equality is checked once at
the block level, rather than repeatedly traversing an array during every walk.
The step comparison below preserves the literal letter and point conventions.

Source: `../source/README.md`; this is a computational refinement of Model.lean.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
inductive BlockTree where
  | leaf : Nat → BlockTree
  | node : BlockTree → BlockTree → BlockTree

def blockGet : BlockTree → Nat → Nat
  | .leaf x, _ => x
  | .node l r, i => if i % 2 == 0 then blockGet l (i / 2) else blockGet r (i / 2)

def treeLookup (t : BlockTree) (n : Nat) : Nat :=
  (blockGet t (n / 128) >>> (15 * (n % 128))) % 32768
lemma treeLookup_eq (t : BlockTree) (a : Array Nat)
    (h : ∀ q : Fin 189, blockGet t q.val = a[q.val]!)
    (x : Point) : treeLookup t x.val = lookup 15 a x.val := by
  unfold treeLookup lookup
  rw [h ⟨x.val / 128, by have := x.isLt; omega⟩]
  rfl

def treeStep (a b c : BlockTree) (l : Fin 4) (x : Point) : Point :=
  ⟨treeLookup (if l.val % 2 == 0 then a else if l.val == 1 then b else c) x.val % 24192,
    Nat.mod_lt _ (by decide)⟩
lemma treeStep_eq (a b c : BlockTree)
    (ha : ∀ q : Fin 189, blockGet a q.val = actionA[q.val]!)
    (hb : ∀ q : Fin 189, blockGet b q.val = actionB[q.val]!)
    (hc : ∀ q : Fin 189, blockGet c q.val = actionBInv[q.val]!) :
    treeStep a b c = step := by
  funext l x
  apply Fin.ext
  fin_cases l
  · change treeLookup a x.val % 24192 = lookup 15 actionA x.val % 24192
    rw [treeLookup_eq a actionA ha]
  · change treeLookup b x.val % 24192 = lookup 15 actionB x.val % 24192
    rw [treeLookup_eq b actionB hb]
  · change treeLookup a x.val % 24192 = lookup 15 actionA x.val % 24192
    rw [treeLookup_eq a actionA ha]
  · change treeLookup c x.val % 24192 = lookup 15 actionBInv x.val % 24192
    rw [treeLookup_eq c actionBInv hc]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
