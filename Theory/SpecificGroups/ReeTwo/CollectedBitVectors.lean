module

public import Theory.SpecificGroups.ReeTwo.CollectedOperations
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Bit-vector evaluation of collected Ree multiplication

Each bit position represents an independent Sylow element. Bitwise operations
simultaneously evaluate the collected core multiplication and cyclic-four
action. Reading any position gives exactly the ambient collected operation.
Consequently the population count of the commuting mask counts precisely the
commuting positions, without expanding a separate product at every position.

Source: Shinoda (1975), (2.3), pp. 81–82, via `CollectedOperations`.
The bit-vector evaluation method follows `SmallEvenAutCountsA512Arithmetic`;
here the width is arbitrary and the full cyclic-four action is supported.
-/

@[expose] public section
namespace ReeTwo.SylowModel.CollectedBitVectors
set_option maxRecDepth 32768
variable {n : ℕ}
def zbit (b : Bool) : ZMod 2 := if b then 1 else 0
theorem zbit_xor : ∀ a b, zbit (a ^^ b) = zbit a + zbit b := by decide +kernel
theorem zbit_and : ∀ a b, zbit (a && b) = zbit a * zbit b := by decide +kernel
theorem zbit_inj : ∀ a b, zbit a = zbit b ↔ a = b := by decide +kernel
structure PackedCore (n : ℕ) where
  b0 : BitVec n
  b1 : BitVec n
  b2 : BitVec n
  b3 : BitVec n
  b4 : BitVec n
  b5 : BitVec n
  b6 : BitVec n
  b7 : BitVec n
  b8 : BitVec n
  b9 : BitVec n
def get (x : PackedCore n) (k : Fin n) : Core := ⟨zbit (x.b0.getLsbD k.val), zbit (x.b1.getLsbD k.val), zbit (x.b2.getLsbD k.val), zbit (x.b3.getLsbD k.val), zbit (x.b4.getLsbD k.val), zbit (x.b5.getLsbD k.val), zbit (x.b6.getLsbD k.val), zbit (x.b7.getLsbD k.val), zbit (x.b8.getLsbD k.val), zbit (x.b9.getLsbD k.val)⟩
def mul (x y : PackedCore n) : PackedCore n where
  b0 := (x.b0 ^^^ y.b0)
  b1 := (x.b1 ^^^ y.b1)
  b2 := (x.b2 ^^^ y.b2)
  b3 := (x.b3 ^^^ y.b3)
  b4 := (x.b4 ^^^ y.b4)
  b5 := ((((x.b5 ^^^ (x.b2 &&& y.b0)) ^^^ (x.b3 &&& y.b0)) ^^^ (x.b1 &&& y.b1)) ^^^ y.b5)
  b6 := ((((x.b6 ^^^ (x.b3 &&& y.b0)) ^^^ (x.b4 &&& y.b0)) ^^^ (x.b2 &&& y.b1)) ^^^ y.b6)
  b7 := ((((x.b7 ^^^ (x.b4 &&& y.b0)) ^^^ (x.b4 &&& y.b1)) ^^^ (x.b3 &&& y.b2)) ^^^ y.b7)
  b8 := ((((x.b8 ^^^ (x.b4 &&& y.b1)) ^^^ (x.b4 &&& y.b2)) ^^^ (x.b3 &&& y.b3)) ^^^ y.b8)
  b9 := (((((((((((((((((((x.b9 ^^^ (x.b3 &&& y.b0)) ^^^ ((x.b2 &&& x.b4) &&& y.b0)) ^^^ ((x.b3 &&& x.b4) &&& y.b0)) ^^^ (x.b8 &&& y.b0)) ^^^ ((x.b2 &&& x.b3) &&& y.b1)) ^^^ (x.b4 &&& y.b1)) ^^^ ((x.b1 &&& x.b4) &&& y.b1)) ^^^ (x.b7 &&& y.b1)) ^^^ ((x.b4 &&& y.b0) &&& y.b1)) ^^^ (x.b2 &&& y.b2)) ^^^ (x.b6 &&& y.b3)) ^^^ ((x.b3 &&& y.b0) &&& y.b3)) ^^^ ((x.b4 &&& y.b0) &&& y.b3)) ^^^ ((x.b2 &&& y.b1) &&& y.b3)) ^^^ (x.b5 &&& y.b4)) ^^^ ((x.b2 &&& y.b0) &&& y.b4)) ^^^ ((x.b3 &&& y.b0) &&& y.b4)) ^^^ ((x.b1 &&& y.b1) &&& y.b4)) ^^^ y.b9)
def step (x : PackedCore n) : PackedCore n where
  b0 := x.b0
  b1 := (x.b0 ^^^ x.b1)
  b2 := ((x.b0 ^^^ x.b1) ^^^ x.b2)
  b3 := (x.b1 ^^^ x.b3)
  b4 := (((x.b0 ^^^ x.b1) ^^^ x.b3) ^^^ x.b4)
  b5 := ((x.b0 ^^^ (x.b0 &&& x.b1)) ^^^ x.b5)
  b6 := ((((x.b0 ^^^ x.b1) ^^^ (x.b0 &&& x.b1)) ^^^ x.b5) ^^^ x.b6)
  b7 := ((((x.b0 ^^^ (x.b0 &&& x.b1)) ^^^ (x.b1 &&& x.b2)) ^^^ x.b6) ^^^ x.b7)
  b8 := ((((((((x.b0 ^^^ x.b1) ^^^ (x.b0 &&& x.b2)) ^^^ (x.b1 &&& x.b2)) ^^^ (x.b1 &&& x.b3)) ^^^ x.b5) ^^^ x.b6) ^^^ x.b7) ^^^ x.b8)
  b9 := (((((((((x.b0 ^^^ x.b1) ^^^ (x.b0 &&& x.b2)) ^^^ (x.b1 &&& x.b2)) ^^^ (x.b1 &&& x.b3)) ^^^ (x.b0 &&& x.b4)) ^^^ ((x.b0 &&& x.b1) &&& x.b4)) ^^^ x.b5) ^^^ x.b6) ^^^ x.b9)
theorem get_mul (x y : PackedCore n) (k : Fin n) :
    get (mul x y) k = Core.mul (get x k) (get y k) := by
  apply Core.ext <;> simp only [get, mul, Core.mul, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, zbit_xor, zbit_and]
theorem get_step (x : PackedCore n) (k : Fin n) :
    get (step x) k = collectedActionStep (get x k) := by
  apply Core.ext <;> simp only [get, step, collectedActionStep, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, zbit_xor, zbit_and]
def select (t : BitVec n) (x y : PackedCore n) : PackedCore n := ⟨x.b0 ^^^ (t &&& (x.b0 ^^^ y.b0)), x.b1 ^^^ (t &&& (x.b1 ^^^ y.b1)), x.b2 ^^^ (t &&& (x.b2 ^^^ y.b2)), x.b3 ^^^ (t &&& (x.b3 ^^^ y.b3)), x.b4 ^^^ (t &&& (x.b4 ^^^ y.b4)), x.b5 ^^^ (t &&& (x.b5 ^^^ y.b5)), x.b6 ^^^ (t &&& (x.b6 ^^^ y.b6)), x.b7 ^^^ (t &&& (x.b7 ^^^ y.b7)), x.b8 ^^^ (t &&& (x.b8 ^^^ y.b8)), x.b9 ^^^ (t &&& (x.b9 ^^^ y.b9))⟩
theorem bool_select (t x y : Bool) : (x ^^ (t && (x ^^ y))) = if t then y else x := by
  cases t <;> cases x <;> cases y <;> rfl
theorem get_select (t : BitVec n) (x y : PackedCore n) (k : Fin n) :
    get (select t x y) k = if t.getLsbD k.val then get y k else get x k := by
  simp only [get, select, BitVec.getLsbD_xor, BitVec.getLsbD_and, bool_select]
  cases t.getLsbD k.val <;> rfl
def action (t₀ t₁ : BitVec n) (x : PackedCore n) : PackedCore n :=
  let y := select t₀ x (step x)
  select t₁ y (step (step y))
theorem get_action (t₀ t₁ : BitVec n) (x : PackedCore n) (k : Fin n) :
    get (action t₀ t₁ x) k = collectedAction
      (Multiplicative.ofAdd ((t₀.getLsbD k.val).toNat + 2*(t₁.getLsbD k.val).toNat : ZMod 4))
      (get x k) := by
  simp only [action, get_select, get_step]
  cases t₀.getLsbD k.val <;> cases t₁.getLsbD k.val <;> rfl
def eqMask (x y : PackedCore n) : BitVec n :=
  ~~~(x.b0 ^^^ y.b0) &&&
    ~~~(x.b1 ^^^ y.b1) &&&
    ~~~(x.b2 ^^^ y.b2) &&&
    ~~~(x.b3 ^^^ y.b3) &&&
    ~~~(x.b4 ^^^ y.b4) &&&
    ~~~(x.b5 ^^^ y.b5) &&&
    ~~~(x.b6 ^^^ y.b6) &&&
    ~~~(x.b7 ^^^ y.b7) &&&
    ~~~(x.b8 ^^^ y.b8) &&&
    ~~~(x.b9 ^^^ y.b9)
theorem eqMask_spec (x y : PackedCore n) (k : Fin n) :
    (eqMask x y).getLsbD k.val = true ↔ get x k = get y k := by
  simp [eqMask, get, Core.mk.injEq, zbit_inj, k.isLt, and_assoc]
def replicate (b : Bool) : BitVec n := if b then BitVec.allOnes n else 0
theorem get_replicate (b : Bool) (k : Fin n) : (replicate (n := n) b).getLsbD k.val = b := by
  cases b <;> simp [replicate, k.isLt]
theorem pop_sum (x : BitVec n) (m : ℕ) :
    x.cpopNatRec m 0 = ∑ k ∈ Finset.range m, (x.getLsbD k).toNat := by
  induction m with
  | zero => simp [BitVec.cpopNatRec]
  | succ m ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, ih, Finset.sum_range_succ, Nat.zero_add]
theorem pop_card (x : BitVec n) :
    (Finset.univ.filter (fun k : Fin n => x.getLsbD k.val = true)).card =
      x.cpopNatRec n 0 := by
  rw [pop_sum, ← Fin.sum_univ_eq_sum_range, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k _
  cases x.getLsbD k.val <;> rfl


structure PackedElement (n : ℕ) where
  core : PackedCore n
  t₀ : BitVec n
  t₁ : BitVec n

def read (x : PackedElement n) (k : Fin n) : SylowModel :=
  ⟨get x.core k, Multiplicative.ofAdd
    ((x.t₀.getLsbD k.val).toNat + 2*(x.t₁.getLsbD k.val).toNat : ZMod 4)⟩
def productCore (x y : PackedElement n) : PackedCore n :=
  mul x.core (action x.t₀ x.t₁ y.core)
theorem get_productCore (x y : PackedElement n) (k : Fin n) :
    get (productCore x y) k = (collectedMul (read x k) (read y k)).left := by
  rw [productCore, get_mul, get_action]
  rfl

def packCore (x : Core) : PackedCore n :=
  ⟨replicate (x.b0 == 1), replicate (x.b1 == 1), replicate (x.b2 == 1), replicate (x.b3 == 1), replicate (x.b4 == 1), replicate (x.b5 == 1), replicate (x.b6 == 1), replicate (x.b7 == 1), replicate (x.b8 == 1), replicate (x.b9 == 1)⟩
theorem zbit_beq : ∀ a : ZMod 2, zbit (a == 1) = a := by decide +kernel
theorem get_packCore (x : Core) (k : Fin n) : get (packCore x) k = x := by
  apply Core.ext <;> simp only [get, packCore, get_replicate, zbit_beq]
def pack (x : SylowModel) : PackedElement n :=
  ⟨packCore x.left, replicate (x.right.toAdd.val % 2 == 1),
    replicate (x.right.toAdd.val / 2 == 1)⟩
theorem read_pack (x : SylowModel) (k : Fin n) : read (pack x) k = x := by
  have ht : ∀ t : FiveFour.Cyclic 4,
      Multiplicative.ofAdd ((t.toAdd.val % 2 == 1).toNat +
        2*(t.toAdd.val / 2 == 1).toNat : ZMod 4) = t := by decide +kernel
  apply SemidirectProduct.ext
  · exact get_packCore x.left k
  · simpa only [read, pack, get_replicate] using ht x.right

def commuteMask (x y : PackedElement n) : BitVec n :=
  eqMask (productCore x y) (productCore y x)
theorem commuteMask_spec (x y : PackedElement n) (k : Fin n) :
    (commuteMask x y).getLsbD k.val = true ↔
      collectedMul (read x k) (read y k) = collectedMul (read y k) (read x k) := by
  rw [commuteMask, eqMask_spec, get_productCore, get_productCore]
  constructor
  · intro h
    apply SemidirectProduct.ext h
    exact mul_comm _ _
  · exact congrArg SemidirectProduct.left
end ReeTwo.SylowModel.CollectedBitVectors
