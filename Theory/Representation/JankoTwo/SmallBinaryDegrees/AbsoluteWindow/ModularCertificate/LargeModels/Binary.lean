module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.Matrix.Basic

/-!
# Packed binary identities over arbitrary characteristic-two fields

The existing binary row-product checker proves identities over `ZMod 2`.
Mapping along its canonical homomorphism into a characteristic-two field
preserves those identities. Boolean checks avoid constructing a large nested
decidable universal proposition. Every successful check is reduced by Lean's
kernel at its concrete use; external matrix calculations are only witnesses.

Application: the ATLAS Hall--Janko matrix candidates of dimensions 36, 84 and
160, recorded in `ModularCertificate/Source.md`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
open Thompson.BinaryMatrix

def checkProduct (n : ℕ) (a b c : Array ℕ) : Bool :=
  (List.range n).all fun i => rowProduct a[i]! b n == c[i]!

def checkInverse (n : ℕ) (a b : Array ℕ) : Bool :=
  (List.range n).all fun i => rowProduct a[i]! b n == 2 ^ i

theorem checkProduct_sound (n : ℕ) (a b c : Array ℕ)
    (h : checkProduct n a b c = true) : decode n a * decode n b = decode n c := by
  apply decode_mul
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem checkInverse_sound (n : ℕ) (a b : Array ℕ)
    (h : checkInverse n a b = true) : decode n a * decode n b = 1 := by
  apply decode_mul_one
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

variable (F : Type*) [Field F] [CharP F 2]

/-- Interpret each binary entry through the canonical characteristic-two map. -/
def eval (n : ℕ) (a : Array ℕ) : Matrix (Fin n) (Fin n) F :=
  (ZMod.castHom (dvd_refl 2) F).mapMatrix (decode n a)

/-- This is the literal entry interpretation used by the original ATLAS files. -/
theorem eval_apply (n : ℕ) (a : Array ℕ) (i j : Fin n) :
    eval F n a i j = if a[i.val]!.testBit j.val then 1 else 0 := by
  simp only [eval, RingHom.mapMatrix_apply, Matrix.map_apply, decode, bit]
  split_ifs <;> simp

theorem eval_product (n : ℕ) (a b c : Array ℕ)
    (h : decode n a * decode n b = decode n c) :
    eval F n a * eval F n b = eval F n c := by
  have hm := congrArg ((ZMod.castHom (dvd_refl 2) F).mapMatrix (m := Fin n)) h
  simpa only [map_mul, eval] using hm

theorem eval_inverse (n : ℕ) (a b : Array ℕ)
    (h : decode n a * decode n b = 1) : eval F n a * eval F n b = 1 := by
  have hm := congrArg ((ZMod.castHom (dvd_refl 2) F).mapMatrix (m := Fin n)) h
  simpa only [map_mul, map_one, eval] using hm

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
