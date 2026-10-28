module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic

/-!
# Balanced checking of selected-row sums and digit parities

A binary tree sums the selected expanded generator rows, skipping zero masks.
Its flattening is the original list, so the result is exactly `Wide.sumRow`.
Balanced digit blocks give the original 1792-column parity checker. Concrete
certificates use separate sum and parity reductions to avoid recomputing sums.
See `../source/README.md` for the fixed ATLAS matrix conventions and provenance.
-/

@[expose] public section
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

theorem sumRow_append (a : Nat) (bs cs : List Nat) :
    Wide.sumRow a (bs ++ cs) = Wide.sumRow a bs + Wide.sumRow (a / 2^bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [Wide.sumRow]
  | cons b bs ih =>
    simp only [List.cons_append, Wide.sumRow, ih, List.length_cons, Nat.add_assoc]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem sumRow_zero (bs : List Nat) : Wide.sumRow 0 bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [Wide.sumRow, ih]

theorem sumRow_mod (a : Nat) (bs : List Nat) :
    Wide.sumRow (a % 2^bs.length) bs = Wide.sumRow a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, Nat.pow_succ', Wide.sumRow]
    rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ih]

inductive Tree where
  | leaf : Nat → Tree
  | node : Nat → Tree → Tree → Tree

def flatten : Tree → List Nat
  | .leaf b => [b]
  | .node _ l r => flatten l ++ flatten r

def Valid : Tree → Prop
  | .leaf _ => True
  | .node k l r => (flatten l).length = k ∧ Valid l ∧ Valid r

def row (a : Nat) : Tree → Nat
  | .leaf b => if a % 2 == 1 then b else 0
  | .node k l r => if a == 0 then 0 else row (a % 2^k) l + row (a / 2^k) r

theorem row_sound (a : Nat) (t : Tree) (h : Valid t) : row a t = Wide.sumRow a (flatten t) := by
  induction t generalizing a with
  | leaf b => simp [row, flatten, Wide.sumRow]
  | node k l r ihl ihr =>
    obtain ⟨hk, hl, hr⟩ := h
    simp only [row]
    split
    · rename_i ha
      have ha' : a = 0 := by simpa using ha
      subst a
      exact (sumRow_zero _).symm
    · rw [ihl _ hl, ihr _ hr, flatten, sumRow_append, ← hk, sumRow_mod]

theorem parity_add (n m x y : Nat) :
    Wide.checkParity (n+m) x y =
      (Wide.checkParity n x y && Wide.checkParity m (x / 4096^n) (y / 2^n)) := by
  induction n generalizing x y with
  | zero => simp [Wide.checkParity]
  | succ n ih =>
    simp only [Nat.succ_add, Wide.checkParity, ih, Bool.and_assoc]
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_succ', ← Nat.pow_succ']

def parityPow : Nat → Nat → Nat → Bool
  | 0, x, y => x % 2 == y % 2
  | k+1, x, y => parityPow k x y && parityPow k (x / 4096^(2^k)) (y / 2^(2^k))

theorem parityPow_eq (k x y : Nat) : parityPow k x y = Wide.checkParity (2^k) x y := by
  induction k generalizing x y with
  | zero => simp [parityPow, Wide.checkParity]
  | succ k ih =>
    simp only [parityPow, ih, Nat.pow_succ, Nat.mul_two, parity_add]

def parity1792 (x y : Nat) : Bool :=
  parityPow 10 x y && parityPow 9 (x / 4096^1024) (y / 2^1024) &&
    parityPow 8 (x / 4096^1536) (y / 2^1536)

theorem parity1792_eq (x y : Nat) : parity1792 x y = Wide.checkParity 1792 x y := by
  rw [show 1792 = 1536 + 256 from rfl, parity_add, show 1536 = 1024 + 512 from rfl,
    parity_add]
  simp only [parity1792, parityPow_eq, show 2^10 = 1024 from rfl,
    show 2^9 = 512 from rfl, show 2^8 = 256 from rfl, show 1024 + 512 = 1536 from rfl]

/-- Integer sums are checked independently of their digit parities. -/
def checkSums (t : Tree) : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, s :: ss => (row a t == s) && checkSums t as ss
  | _, _ => false

def checkParities : List Nat → List Nat → Bool
  | [], [] => true
  | s :: ss, c :: cs => parity1792 s c && checkParities ss cs
  | _, _ => false

/-- Recover the literal original product checker from the two bounded checks. -/
theorem checks_sound (a c s w : List Nat) (t : Tree)
    (hv : Valid t) (hf : flatten t = w)
    (hs : checkSums t a s = true) (hp : checkParities s c = true) :
    Wide.checkRows 1792 a w c = true := by
  induction a generalizing s c with
  | nil =>
    cases s with
    | nil => cases c <;> simp_all [checkParities, Wide.checkRows]
    | cons _ _ => simp [checkSums] at hs
  | cons a as ih =>
    cases s with
    | nil => simp [checkSums] at hs
    | cons s ss =>
      cases c with
      | nil => simp [checkParities] at hp
      | cons c cs =>
        simp only [checkSums, Bool.and_eq_true, beq_iff_eq] at hs
        simp only [checkParities, Bool.and_eq_true, parity1792_eq] at hp
        exact RightCertificate.product_cons a c s as w cs
          (by rw [← hf, ← row_sound a t hv]; exact hs.1) hp.1 (ih cs ss hs.2 hp.2)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
