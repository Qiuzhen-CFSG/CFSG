module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic


/-!
# A bounded binary four-matrix form certificate

Fix the companion matrix C of X⁴+X³+X²+X+1. An involution A for which
(AC)⁶ = 1 preserves one of the three nonsingular alternating forms fixed
by C. The sixteen input bits are checked in sixteen blocks of 4096 cases.
Kernel reduction checks each block; the encoding is proved to
respect ordinary matrix multiplication and transpose.

This is the finite linear-algebra step used to construct the invariant
form of the native hexad action in Aschbacher--Smith H.14.3(3), printed
p.397. No classification of representations is assumed.
-/

-- Checking the bounded certificates sequentially limits peak memory.
set_option Elab.async false

namespace BinaryFourSymmetricForm
public abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)
namespace Packed
def mv (a : BitVec 16) (x : BitVec 4) : BitVec 4 :=
  (if x[0] then a.extractLsb' 0 4 else 0) ^^^
  (if x[1] then a.extractLsb' 4 4 else 0) ^^^
  (if x[2] then a.extractLsb' 8 4 else 0) ^^^
  (if x[3] then a.extractLsb' 12 4 else 0)
def mm (a b : BitVec 16) : BitVec 16 :=
  mv a (b.extractLsb' 12 4) ++ mv a (b.extractLsb' 8 4) ++
    mv a (b.extractLsb' 4 4) ++ mv a (b.extractLsb' 0 4)
def tp (a : BitVec 16) : BitVec 16 :=
  (BitVec.ofBool a[15]) ++ (BitVec.ofBool a[11]) ++ (BitVec.ofBool a[7]) ++ (BitVec.ofBool a[3]) ++
  (BitVec.ofBool a[14]) ++ (BitVec.ofBool a[10]) ++ (BitVec.ofBool a[6]) ++ (BitVec.ofBool a[2]) ++
  (BitVec.ofBool a[13]) ++ (BitVec.ofBool a[9]) ++ (BitVec.ofBool a[5]) ++ (BitVec.ofBool a[1]) ++
  (BitVec.ofBool a[12]) ++ (BitVec.ofBool a[8]) ++ (BitVec.ofBool a[4]) ++ (BitVec.ofBool a[0])
def pres (a b : BitVec 16) : Prop := mm (mm (tp a) b) a = b

def pow6 (a : BitVec 16) : BitVec 16 :=
  let a3 := mm (mm a a) a
  mm a3 a3

def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0
def toMat (a : BitVec 16) : Mat := fun i j => bitVal (a.getLsbD (4*j.val+i.val))
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
lemma toMat_tp (a : BitVec 16) : toMat (tp a) = (toMat a).transpose := by
  ext i j
  change bitVal ((tp a).getLsbD (4*j.val+i.val)) = bitVal (a.getLsbD (4*i.val+j.val))
  apply congrArg bitVal
  fin_cases i <;> fin_cases j <;>
    simp only [tp, BitVec.getLsbD_append] <;> norm_num
lemma toMat_one : toMat 0x8421 = 1 := by decide +kernel
lemma toMat_pow6 (a : BitVec 16) : toMat (pow6 a) = toMat a ^ 6 := by
  simp only [pow6, toMat_mm]
  noncomm_ring
lemma toMat_injective : Function.Injective toMat := by
  intro a b h
  have hb : Function.Injective bitVal := by decide +kernel
  have hh (i j : Fin 4) := hb (congrArg (fun m : Mat => m i j) h)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h' := hh ⟨k % 4, Nat.mod_lt _ (by decide)⟩ ⟨k / 4, by omega⟩
  have he : 4 * (k / 4) + k % 4 = k := by omega
  exact he ▸ h'

def pack (a : Mat) : BitVec 16 :=
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
lemma toMat_pack (a : Mat) : toMat (pack a) = a := by
  have hb : ∀ x : ZMod 2, bitVal (x == 1) = x := by decide +kernel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [toMat, pack, BitVec.getLsbD_append] <;> norm_num [hb] <;> rfl

def Check (i : Fin 16) : Prop :=
  ∀ j : Fin 16, ∀ k : Fin 256,
    let a : BitVec 16 := BitVec.ofFin (w := 4) i ++
      BitVec.ofFin (w := 4) j ++ BitVec.ofFin (w := 8) k
    mm a a = 0x8421 → pow6 (mm a 0xf842) = 0x8421 →
      pres a 0x318c ∨ pres a 0x4a52 ∨ pres a 0x7bde

theorem check0 : Check 0 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check1 : Check 1 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check2 : Check 2 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check3 : Check 3 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check4 : Check 4 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check5 : Check 5 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check6 : Check 6 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check7 : Check 7 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check8 : Check 8 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check9 : Check 9 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check10 : Check 10 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check11 : Check 11 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check12 : Check 12 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check13 : Check 13 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check14 : Check 14 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem check15 : Check 15 := by
  unfold Check
  dsimp only [pres]
  decide +kernel

theorem checked (i : Fin 16) : Check i := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15

theorem certificate (a : BitVec 16)
    (h2 : mm a a = 0x8421) (h6 : pow6 (mm a 0xf842) = 0x8421) :
    pres a 0x318c ∨ pres a 0x4a52 ∨ pres a 0x7bde := by
  have h := checked (a.extractLsb' 12 4).toFin
    (a.extractLsb' 8 4).toFin (a.extractLsb' 0 8).toFin
  have he : a.extractLsb' 12 4 ++ a.extractLsb' 8 4 ++ a.extractLsb' 0 8 = a := by
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 12 = 8 + 4)]
    exact BitVec.extractLsb'_append_extractLsb'
  change mm (a.extractLsb' 12 4 ++ a.extractLsb' 8 4 ++ a.extractLsb' 0 8)
      (a.extractLsb' 12 4 ++ a.extractLsb' 8 4 ++ a.extractLsb' 0 8) = _ → _ at h
  rw [he] at h
  exact h h2 h6

end Packed

/-- Companion matrix of the fifth cyclotomic polynomial over F₂. -/
@[expose] public def C : Mat := !![0,0,0,1; 1,0,0,1; 0,1,0,1; 0,0,1,1]

private def form : Fin 3 → Mat :=
  ![Packed.toMat 0x318c, Packed.toMat 0x4a52, Packed.toMat 0x7bde]

private theorem form_alt (j : Fin 3) : (form j).toBilin'.IsAlt := by
  revert j
  change ∀ j : Fin 3, ∀ v : Fin 4 → ZMod 2, (form j).toBilin' v v = 0
  decide +kernel

private theorem form_det (j : Fin 3) : (form j).det ≠ 0 := by
  revert j
  decide +kernel

private theorem form_five (j : Fin 3) : C.transpose * form j * C = form j := by
  revert j
  decide +kernel

/-- The normalized (2,5,6) relations force a preserved nonsingular alternating form. -/
public theorem matrixCertificate (A : Mat) (h2 : A ^ 2 = 1) (h6 : (A * C) ^ 6 = 1) :
    ∃ B : Mat, B.toBilin'.IsAlt ∧ B.toBilin'.Nondegenerate ∧
      A.transpose * B * A = B ∧ C.transpose * B * C = B := by
  let a := Packed.pack A
  have ha : Packed.toMat a = A := Packed.toMat_pack A
  have hc : Packed.toMat 0xf842 = C := by decide +kernel
  have h2' : Packed.mm a a = 0x8421 := by
    apply Packed.toMat_injective
    rw [Packed.toMat_mm, ha, Packed.toMat_one, ← pow_two, h2]
  have h6' : Packed.pow6 (Packed.mm a 0xf842) = 0x8421 := by
    apply Packed.toMat_injective
    rw [Packed.toMat_pow6, Packed.toMat_mm, ha, hc, Packed.toMat_one, h6]
  have hp (b : BitVec 16) (h : Packed.pres a b) :
      A.transpose * Packed.toMat b * A = Packed.toMat b := by
    have hh := congrArg Packed.toMat h
    simpa only [Packed.toMat_mm, Packed.toMat_tp, ha] using hh
  have finish (j : Fin 3) (h : A.transpose * form j * A = form j) :
      ∃ B : Mat, B.toBilin'.IsAlt ∧ B.toBilin'.Nondegenerate ∧
        A.transpose * B * A = B ∧ C.transpose * B * C = B :=
    ⟨form j, form_alt j,
      LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (form_det j),
      h, form_five j⟩
  rcases Packed.certificate a h2' h6' with h | h | h
  · exact finish 0 (hp _ h)
  · exact finish 1 (hp _ h)
  · exact finish 2 (hp _ h)

end BinaryFourSymmetricForm
