module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.Blocks
/-!
# Balanced packed row multiplication for the degree-320 product relation

A binary tree groups the same selected row sums as `skipRow`. Each node
records the power of two at which the left and right row intervals split.
The kernel checks these divisors and the flattened rows independently of
any matrix products. The append identity proves that evaluating the tree
is exactly the existing packed multiplication, with no change of basis or
transpose. Bounded row checks then feed the original block assembly.

The concrete consumers are the powers of the literal ATLAS product in
`ProductOrder23`. Source: John Bray, ATLAS M24G1-P1; matrix attribution and
unchanged hashes are in `Degree320Pair/source/`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.Order23.Balanced
open MatrixCertificates
inductive Tree where
| leaf (rows : List Nat)
| node (divisor : Nat) (left right : Tree)
def rows : Tree → List Nat
| .leaf bs => bs
| .node _ l r => rows l ++ rows r
def valid : Tree → Bool
| .leaf _ => true
| .node q l r => (q == 2^(rows l).length) && valid l && valid r
def eval (a : Nat) : Tree → Nat
| .leaf bs => skipRow a bs
| .node q l r => eval a l ^^^ eval (a / q) r
def check : List Nat → Tree → List Nat → Bool
| [], _, [] => true
| a::as, t, c::cs => (eval a t == c) && check as t cs
| _, _, _ => false

theorem skipRow_append (a : Nat) (bs cs : List Nat) :
    skipRow a (bs ++ cs) = skipRow a bs ^^^ skipRow (a / 2^bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [skipRow]
  | cons b bs ih =>
    simp only [List.cons_append, List.length_cons, skipRow, ih, Nat.div_div_eq_div_mul,
      pow_succ, Nat.mul_comm (2 ^ bs.length) 2]
    split <;> simp_all [Nat.xor_assoc]

theorem eval_eq (t : Tree) (h : valid t = true) (a : Nat) :
    eval a t = skipRow a (rows t) := by
  induction t generalizing a with
  | leaf bs => rfl
  | node q l r il ir =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
    rw [eval, il h.1.2, ir h.2, rows, skipRow_append, h.1.1]

theorem check_eq (a c : List Nat) (t : Tree) (h : valid t = true) :
    check a t c = checkRows a (rows t) c := by
  induction a generalizing c with
  | nil => cases c <;> rfl
  | cons x xs ih => cases c <;> simp [check, checkRows, eval_eq t h, skipRow_eq, ih]

theorem checked (a b c : List Nat) (t : Tree) (hv : valid t = true)
    (hb : rows t = b) (h : check a t c = true) : Checked a b c := by
  refine ⟨?_⟩
  rwa [check_eq a c t hv, hb] at h
theorem checked_replace (a b c al cl : List Nat) (t : Tree)
    (ha : a = al) (hc : c = cl) (hv : valid t = true) (hb : rows t = b)
    (h : check al t cl = true) : Checked a b c := by
  rw [ha, hc]
  exact checked al b cl t hv hb h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.Order23.Balanced
