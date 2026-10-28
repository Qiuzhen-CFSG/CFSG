module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic

/-!
# Balanced exact integer sums and digit parity

The tree is a rebracketing of the unchanged sequential `Wide.sumRow`.
Checked subtree lengths justify each division of its coefficient mask.
Balanced digit tests recover exactly `Wide.checkParity` for all 1792 columns.
The concrete consumers certify the final two left-expression products.
See `source/README.md` for attribution and measurements.
-/

@[expose] public section
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts

theorem sumRow_append (a : Nat) (bs cs : List Nat) :
    Wide.sumRow a (bs ++ cs) = Wide.sumRow a bs + Wide.sumRow (a / 2^bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [Wide.sumRow]
  | cons b bs ih =>
    simp [Wide.sumRow, ih, pow_succ', Nat.div_div_eq_div_mul, Nat.add_assoc]

theorem checkParity_add (n m x y : Nat) :
    Wide.checkParity (n+m) x y =
      (Wide.checkParity n x y && Wide.checkParity m (x / 4096^n) (y / 2^n)) := by
  induction n generalizing x y with
  | zero => simp [Wide.checkParity]
  | succ n ih =>
    simp only [Nat.succ_add, Wide.checkParity, ih, Bool.and_assoc]
    simp [pow_succ', Nat.div_div_eq_div_mul]

inductive SumTree where
  | leaf : List Nat → SumTree
  | node : Nat → SumTree → SumTree → SumTree

def SumTree.flatten : SumTree → List Nat
  | .leaf bs => bs
  | .node _ l r => l.flatten ++ r.flatten

def SumTree.Valid : SumTree → Prop
  | .leaf _ => True
  | .node n l r => l.flatten.length = n ∧ l.Valid ∧ r.Valid

def SumTree.check : SumTree → Bool
  | .leaf _ => true
  | .node n l r => (l.flatten.length == n) && l.check && r.check

theorem SumTree.valid_of_check (t : SumTree) (ht : t.check = true) : t.Valid := by
  induction t with
  | leaf bs => trivial
  | node n l r ihl ihr =>
    simp only [check, Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨ht.1.1, ihl ht.1.2, ihr ht.2⟩

def SumTree.eval (a : Nat) : SumTree → Nat
  | .leaf bs => Wide.sumRow a bs
  | .node n l r => l.eval a + r.eval (a / 2^n)

theorem SumTree.eval_eq (a : Nat) (t : SumTree) (ht : t.Valid) :
    t.eval a = Wide.sumRow a t.flatten := by
  induction t generalizing a with
  | leaf bs => rfl
  | node n l r ihl ihr =>
    obtain ⟨hn, hl, hr⟩ := ht
    rw [eval, flatten, sumRow_append, ihl _ hl, ihr _ hr, hn]

def parityTree : Nat → Nat → Nat → Nat → Bool
  | 0, n, x, y => Wide.checkParity n x y
  | h+1, n, x, y => parityTree h n x y &&
      parityTree h n (x / 4096^(n*2^h)) (y / 2^(n*2^h))

theorem parityTree_eq (h n x y : Nat) :
    parityTree h n x y = Wide.checkParity (n*2^h) x y := by
  induction h generalizing x y with
  | zero => simp [parityTree]
  | succ h ih =>
    rw [parityTree, ih, ih]
    have he : n * 2^(h+1) = n * 2^h + n * 2^h := by rw [pow_succ, ← Nat.mul_assoc, Nat.mul_two]
    rw [he, checkParity_add]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts
