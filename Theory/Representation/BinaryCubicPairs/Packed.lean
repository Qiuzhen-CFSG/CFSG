module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Packed coordinates for pairs of binary cubic actors

Four-bit vectors and sixteen-bit matrices encode the ordinary vector space
and matrix algebra over F₂. The comparison lemmas preserve addition, matrix
multiplication and matrix-vector action. They provide the small, checked
arithmetic used in the cubic-pair argument for regular cyclic normal closures.

The intended application is the noncommuting branch of Aschbacher--Smith
E.6.24, printed p.255. These encoding identities have no group classification
hypotheses or conclusions.
-/

@[expose] public section
namespace BinaryCubicPairs
abbrev CoordinateVector := Fin 4 → ZMod 2
abbrev CoordinateMatrix := Matrix (Fin 4) (Fin 4) (ZMod 2)
namespace Packed

def mv (a : BitVec 16) (x : BitVec 4) : BitVec 4 :=
  (if x[0] then a.extractLsb' 0 4 else 0) ^^^
  (if x[1] then a.extractLsb' 4 4 else 0) ^^^
  (if x[2] then a.extractLsb' 8 4 else 0) ^^^
  (if x[3] then a.extractLsb' 12 4 else 0)
def mm (a b : BitVec 16) : BitVec 16 :=
  mv a (b.extractLsb' 12 4) ++ mv a (b.extractLsb' 8 4) ++
    mv a (b.extractLsb' 4 4) ++ mv a (b.extractLsb' 0 4)
def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0
def toMat (a : BitVec 16) : CoordinateMatrix := fun i j => bitVal (a.getLsbD (4*j.val+i.val))
lemma bitVal_xor (a b : Bool) : bitVal (a ^^ b) = bitVal a + bitVal b := by
  cases a <;> cases b <;> decide
lemma bitVal_and (a b : Bool) : bitVal (a && b) = bitVal a * bitVal b := by
  cases a <;> cases b <;> decide
lemma mm_column (a b : BitVec 16) (j : Fin 4) :
    (mm a b).extractLsb' (4*j.val) 4 = mv a (b.extractLsb' (4*j.val) 4) := by
  have h (u v w z : BitVec 4) (n : Nat) :
      (u ++ v ++ w ++ z).extractLsb' (n+4) 4 = (u ++ v ++ w).extractLsb' n 4 :=
    (BitVec.extractLsb'_append_eq_of_le (xhi := u ++ v ++ w) (xlo := z)
      (len := 4) (by omega : 4 ≤ n+4)).trans (by congr 1)
  have h' (u v w : BitVec 4) (n : Nat) :
      (u ++ v ++ w).extractLsb' (n+4) 4 = (u ++ v).extractLsb' n 4 :=
    (BitVec.extractLsb'_append_eq_of_le (xhi := u ++ v) (xlo := w)
      (len := 4) (by omega : 4 ≤ n+4)).trans (by congr 1)
  fin_cases j
  · exact BitVec.extractLsb'_append_eq_right
  · exact (h _ _ _ _ 0).trans BitVec.extractLsb'_append_eq_right
  · exact (h _ _ _ _ 4).trans ((h' _ _ _ 0).trans BitVec.extractLsb'_append_eq_right)
  · exact (h _ _ _ _ 8).trans ((h' _ _ _ 4).trans BitVec.extractLsb'_append_eq_left)
lemma mv_bit (a : BitVec 16) (x : BitVec 4) (i : Fin 4) :
    (mv a x).getLsbD i.val =
      ((a.getLsbD i.val && x.getLsbD 0) ^^
      (a.getLsbD (4+i.val) && x.getLsbD 1) ^^
      (a.getLsbD (8+i.val) && x.getLsbD 2) ^^
      (a.getLsbD (12+i.val) && x.getLsbD 3)) := by
  have hi := i.isLt
  generalize h0 : x[0] = b0
  generalize h1 : x[1] = b1
  generalize h2 : x[2] = b2
  generalize h3 : x[3] = b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [mv, h0, h1, h2, h3, hi]
lemma mm_bit (a b : BitVec 16) (i j : Fin 4) :
    (mm a b).getLsbD (4*j.val+i.val) =
      ((a.getLsbD i.val && b.getLsbD (4*j.val)) ^^
      (a.getLsbD (4+i.val) && b.getLsbD (4*j.val+1)) ^^
      (a.getLsbD (8+i.val) && b.getLsbD (4*j.val+2)) ^^
      (a.getLsbD (12+i.val) && b.getLsbD (4*j.val+3))) := by
  have h := congrArg (fun x : BitVec 4 => x.getLsbD i.val) (mm_column a b j)
  rw [mv_bit] at h
  simpa [BitVec.getLsbD_extractLsb', i.isLt] using h
lemma toMat_mm (a b : BitVec 16) : toMat (mm a b) = toMat a * toMat b := by
  ext i j
  change bitVal ((mm a b).getLsbD (4*j.val+i.val)) = _
  rw [mm_bit]
  simp only [bitVal_xor, bitVal_and]
  simp [Matrix.mul_apply, Fin.sum_univ_succ, toMat, add_assoc]
lemma toMat_one : toMat 0x8421 = 1 := by decide +kernel
lemma toMat_injective : Function.Injective toMat := by
  intro a b h
  have hb : Function.Injective bitVal := by decide +kernel
  have hh (i j : Fin 4) := hb (congrArg (fun m : CoordinateMatrix => m i j) h)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h' := hh ⟨k % 4, Nat.mod_lt _ (by decide)⟩ ⟨k / 4, by omega⟩
  have he : 4 * (k / 4) + k % 4 = k := by omega
  exact he ▸ h'

def pack (a : CoordinateMatrix) : BitVec 16 :=
  BitVec.ofBool (a 3 3 == 1) ++
    BitVec.ofBool (a 2 3 == 1) ++
    BitVec.ofBool (a 1 3 == 1) ++
    BitVec.ofBool (a 0 3 == 1) ++
    BitVec.ofBool (a 3 2 == 1) ++
    BitVec.ofBool (a 2 2 == 1) ++
    BitVec.ofBool (a 1 2 == 1) ++
    BitVec.ofBool (a 0 2 == 1) ++
    BitVec.ofBool (a 3 1 == 1) ++
    BitVec.ofBool (a 2 1 == 1) ++
    BitVec.ofBool (a 1 1 == 1) ++
    BitVec.ofBool (a 0 1 == 1) ++
    BitVec.ofBool (a 3 0 == 1) ++
    BitVec.ofBool (a 2 0 == 1) ++
    BitVec.ofBool (a 1 0 == 1) ++
    BitVec.ofBool (a 0 0 == 1)
lemma toMat_pack (a : CoordinateMatrix) : toMat (pack a) = a := by
  have hb : ∀ x : ZMod 2, bitVal (x == 1) = x := by decide +kernel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [toMat, pack, BitVec.getLsbD_append] <;> norm_num [hb] <;> rfl

def toVec (x : BitVec 4) : CoordinateVector := fun i => bitVal (x.getLsbD i.val)

def packVec (x : CoordinateVector) : BitVec 4 :=
  BitVec.ofBool (x 3 == 1) ++ BitVec.ofBool (x 2 == 1) ++
    BitVec.ofBool (x 1 == 1) ++ BitVec.ofBool (x 0 == 1)

lemma toVec_packVec (x : CoordinateVector) : toVec (packVec x) = x := by
  have hb : ∀ z : ZMod 2, bitVal (z == 1) = z := by decide +kernel
  ext i
  fin_cases i <;> simp only [toVec, packVec, BitVec.getLsbD_append] <;>
    norm_num [hb] <;> rfl

lemma toVec_injective : Function.Injective toVec := by
  intro x y h
  have hb : Function.Injective bitVal := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  exact hb (congrFun h ⟨k, hk⟩)

lemma toVec_zero : toVec 0 = 0 := by decide +kernel

lemma toVec_xor (x y : BitVec 4) : toVec (x ^^^ y) = toVec x + toVec y := by
  ext i
  simp only [toVec, BitVec.getLsbD_xor, Pi.add_apply]
  exact bitVal_xor _ _

lemma toVec_mv (a : BitVec 16) (x : BitVec 4) :
    toVec (mv a x) = (toMat a).mulVec (toVec x) := by
  ext i
  change bitVal ((mv a x).getLsbD i.val) = _
  rw [mv_bit]
  simp only [bitVal_xor, bitVal_and]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, toMat, toVec, add_assoc]

lemma toMat_xor (a b : BitVec 16) : toMat (a ^^^ b) = toMat a + toMat b := by
  ext i j
  simp only [toMat, BitVec.getLsbD_xor, Matrix.add_apply]
  exact bitVal_xor _ _

lemma toMat_zero : toMat 0 = 0 := by decide +kernel

lemma toVec_surjective : Function.Surjective toVec :=
  fun x => ⟨packVec x, toVec_packVec x⟩

end Packed
end BinaryCubicPairs
