module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Certificate

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveLocal

/-!
# Simultaneous evaluation of binary matrix relations

Four natural-number bit masks represent the four matrix entries at each of
256 assignments to two binary matrices. Bitwise XOR and AND implement matrix
addition and multiplication. The interpretation lemmas connect this computation
to the exact `Certificate.wordValue` and `Relation.value` conventions.

This is the arithmetic layer for the finite matrix calculation associated with
the J₂ five-corner certificate; no group-algebra identification is used here.
The data source and source use are documented in `FiveCorner/Certificate.lean`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
open Certificate
structure Packed where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq

def padd (x y : Packed) : Packed :=
  ⟨x.a ^^^ y.a, x.b ^^^ y.b, x.c ^^^ y.c, x.d ^^^ y.d⟩
def pmul (x y : Packed) : Packed :=
  ⟨(x.a &&& y.a) ^^^ (x.b &&& y.c), (x.a &&& y.b) ^^^ (x.b &&& y.d),
   (x.c &&& y.a) ^^^ (x.d &&& y.c), (x.c &&& y.b) ^^^ (x.d &&& y.d)⟩
def mask : Nat := 2^256-1
def pone : Packed := ⟨mask,0,0,mask⟩
def pzero : Packed := ⟨0,0,0,0⟩
def pword (x y : Packed) (n : Nat) : Packed :=
  ((n.bits.dropLast.reverse).map fun b => if b then y else x).foldr pmul pone

def entry (p : Nat) (n : Nat) : ZMod 2 := if n.testBit p then 1 else 0

def peek (p : Nat) (x : Packed) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![entry p x.a, entry p x.b; entry p x.c, entry p x.d]

theorem entry_xor (p a b : Nat) : entry p (a ^^^ b) = entry p a + entry p b := by
  simp only [entry, Nat.testBit_xor]
  cases a.testBit p <;> cases b.testBit p <;> decide

theorem entry_and (p a b : Nat) : entry p (a &&& b) = entry p a * entry p b := by
  simp only [entry, Nat.testBit_and]
  cases a.testBit p <;> cases b.testBit p <;> decide

theorem at_add (p : Nat) (x y : Packed) : peek p (padd x y) = peek p x + peek p y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peek, padd, entry_xor]

theorem at_mul (p : Nat) (x y : Packed) : peek p (pmul x y) = peek p x * peek p y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peek, pmul, Matrix.mul_apply, Fin.sum_univ_two, entry_xor, entry_and]

def px : Packed := ⟨115790322417210952336529717160220497262186272106556906860092653394915770695680, 115792089210356248762697446947946071893095522863849111501270640965525260206080, 115792089237316195417293883273301227089774477609353836086800156426807153786880, 115792089237316195423570985008687907852929702298719625575994209400481361428480⟩
def py : Packed := ⟨77194726158210796949047323339125271902179989777093709359638389338608753093290, 92633671389852956338856788006950326282615987732512451231566067206330503711948, 108980789870415242751596221184647442685430573802955824978313020242741769072880, 115341536360906404779899502576747487978354537254490211650198994186870666100480⟩
def pvalue (r : Relation) : Packed :=
  (r.terms.map (pword px py)).foldr padd pzero

def bad (x : Packed) : Nat := x.a ||| x.b ||| x.c ||| x.d

def forbidden (rs : List Relation) (i j : Fin 9) : Nat :=
  (rs.filter fun r => r.first == i && r.second == j).foldr
    (fun r s => bad (pvalue r) ||| s) 0

def decode (n : Fin 16) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![entry 0 n.val, entry 1 n.val; entry 2 n.val, entry 3 n.val]

theorem decode_surjective : Function.Surjective decode := by decide +kernel

theorem peek_px : ∀ a b : Fin 16, peek (16 * a.val + b.val) px = decode a := by
  decide +kernel

theorem peek_py : ∀ a b : Fin 16, peek (16 * a.val + b.val) py = decode b := by
  decide +kernel

theorem peek_zero (p : Nat) : peek p pzero = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peek, pzero, entry]

theorem peek_one : ∀ p : Fin 256, peek p.val pone = 1 := by decide +kernel

theorem peek_prod (p : Fin 256) (l : List Packed) :
    peek p.val (l.foldr pmul pone) = (l.map (peek p.val)).prod := by
  induction l with
  | nil => exact peek_one p
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.prod_cons, at_mul] using congrArg (peek p.val a * ·) ih

theorem peek_sum (p : Nat) (l : List Packed) :
    peek p (l.foldr padd pzero) = (l.map (peek p)).sum := by
  induction l with
  | nil => exact peek_zero p
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.sum_cons, at_add] using congrArg (peek p a + ·) ih

theorem peek_word (p : Fin 256) (x y : Packed) (n : Nat) :
    peek p.val (pword x y n) = wordValue (peek p.val x) (peek p.val y) n := by
  rw [pword, peek_prod]
  simp only [wordValue, List.map_map, Function.comp_def, apply_ite]

theorem peek_value (p : Fin 256) (r : Relation) :
    peek p.val (pvalue r) = (r.terms.map (wordValue (peek p.val px) (peek p.val py))).sum := by
  rw [pvalue, peek_sum]
  simp only [List.map_map, Function.comp_def, peek_word]

theorem entry_zero (p n : Nat) (h : entry p n = 0) : n.testBit p = false := by
  cases hn : n.testBit p <;> simp_all [entry]

theorem bad_zero (p : Nat) (q : Packed) (h : peek p q = 0) : (bad q).testBit p = false := by
  have ha : entry p q.a = 0 := congrArg (fun m => m 0 0) h
  have hb : entry p q.b = 0 := congrArg (fun m => m 0 1) h
  have hc : entry p q.c = 0 := congrArg (fun m => m 1 0) h
  have hd : entry p q.d = 0 := congrArg (fun m => m 1 1) h
  simp only [bad, Nat.testBit_or, entry_zero p q.a ha, entry_zero p q.b hb,
    entry_zero p q.c hc, entry_zero p q.d hd]
  rfl

theorem forbidden_false (rs : List Relation) (x : Fin 9 → Fin 16)
    (h : ∀ r ∈ rs, r.value (fun i => decode (x i)) = 0)
    (i j : Fin 9) : (forbidden rs i j).testBit (16 * (x i).val + (x j).val) = false := by
  let p : Fin 256 := ⟨16 * (x i).val + (x j).val, by have := (x i).isLt; have := (x j).isLt; omega⟩
  have hv : ∀ r ∈ rs.filter (fun r => r.first == i && r.second == j),
      (bad (pvalue r)).testBit p.val = false := by
    intro r hr
    obtain ⟨hr, he⟩ := List.mem_filter.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    apply bad_zero
    rw [peek_value]
    change (r.terms.map (wordValue (peek (16 * (x i).val + (x j).val) px)
      (peek (16 * (x i).val + (x j).val) py))).sum = 0
    rw [peek_px, peek_py]
    simpa only [Relation.value, he.1, he.2] using h r hr
  change ((rs.filter (fun r => r.first == i && r.second == j)).foldr
    (fun r s => bad (pvalue r) ||| s) 0).testBit p.val = false
  generalize rs.filter (fun r => r.first == i && r.second == j) = l at *
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.testBit_or, hv a (List.mem_cons_self)]
    exact ih (fun r hr => hv r (List.mem_cons_of_mem a hr))
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
