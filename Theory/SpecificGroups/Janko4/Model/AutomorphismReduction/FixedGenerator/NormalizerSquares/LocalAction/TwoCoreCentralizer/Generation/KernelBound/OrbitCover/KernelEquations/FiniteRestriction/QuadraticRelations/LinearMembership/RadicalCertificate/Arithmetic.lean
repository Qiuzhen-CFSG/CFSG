module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Coordinates

/-!
# Arithmetic for the radical certificate

Binary XOR combinations decode to linear combinations of alternating forms.
The finite certificates below use this interface with the original exterior
generators, rather than treating numerical nullspace vectors as axioms.
See ../../source/README.md for the ATLAS column convention and provenance.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates

/-- Sequential bit scan, avoiding an indexed enumeration at every XOR step. -/
def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ scan (x >>> 1) ys

theorem scan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    scan x (List.ofFn f) =
      xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [scan, xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, scan, xorList, ih]
    congr 1
    apply congrArg xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

theorem scan_eq {n : ℕ} (x : ℕ) (v : Vector ℕ n) :
    scan x v.toList = rectRowProduct x v := by
  have hv : List.ofFn v.get = v.toList :=
    Vector.toList_ofFn.symm.trans (congrArg Vector.toList
      (show Vector.ofFn v.get = v from Vector.ofFn_getElem))
  rw [← hv, scan_ofFn]
  rfl

theorem decodeExteriorForm_xor (x y : ℕ) :
    decodeExteriorForm (x ^^^ y) = decodeExteriorForm x + decodeExteriorForm y := by
  ext i j
  simp only [decodeExteriorForm, Matrix.add_apply]
  by_cases hij : i < j
  · simpa only [hij, if_pos] using bit_xor x y (exteriorIndex i j)
  · by_cases hji : j < i
    · simpa only [hij, hji, if_pos, if_false] using bit_xor x y (exteriorIndex j i)
    · simp only [hij, hji, if_false, add_zero]

theorem decodeExteriorForm_zero : decodeExteriorForm 0 = 0 := by
  ext i j
  simp [decodeExteriorForm]

theorem decodeExteriorForm_xorList (xs : List ℕ) :
    decodeExteriorForm (xorList xs) = (xs.map decodeExteriorForm).sum := by
  induction xs with
  | nil => exact decodeExteriorForm_zero
  | cons x xs ih => simp only [xorList, decodeExteriorForm_xor, List.map_cons,
      List.sum_cons, ih]

theorem decodeExteriorForm_combination {n : ℕ} (c : ℕ) (xs : Vector ℕ n) :
    decodeExteriorForm (rectRowProduct c xs) =
      ∑ i : Fin n, bit c i.val • decodeExteriorForm (xs.get i) := by
  rw [rectRowProduct, decodeExteriorForm_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : c.testBit i.val <;> simp [h, bit, decodeExteriorForm_zero]

theorem rectDecode_eq_exterior (xs : Vector ℕ 112) (x : ℕ)
    (h : ∀ i j : Fin 112, (xs.get i).testBit j.val =
      if i < j then x.testBit (exteriorIndex i j)
      else if j < i then x.testBit (exteriorIndex j i) else false) :
    rectDecode 112 xs = decodeExteriorForm x := by
  ext i j
  simp only [rectDecode, bit, h, decodeExteriorForm]
  by_cases hij : i < j <;> by_cases hji : j < i <;> simp [hij, hji]

theorem rectDecode_transpose {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (h : ∀ i : Fin m, ∀ j : Fin n,
      (xs.get i).testBit j.val = (ys.get j).testBit i.val) :
    (rectDecode n xs)ᵀ = rectDecode m ys := by
  ext i j
  simp only [Matrix.transpose_apply, rectDecode, bit, h]

theorem rectDecode_zero {m n : ℕ} :
    rectDecode n (Vector.replicate m 0) = 0 := by
  ext i j
  simp [rectDecode, bit, Vector.get]

theorem rectProduct_zero {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (h : ∀ i, rectRowProduct (xs.get i) ys = 0) :
    rectDecode n xs * rectDecode k ys = 0 := by
  rw [← rectDecode_zero]
  apply rectProduct_eq
  simpa [Vector.get] using h

theorem rectDecode_combination {m n t : ℕ} (c : ℕ)
    (xs : Vector (Vector ℕ m) t) :
    rectDecode n (Vector.ofFn (fun i =>
      rectRowProduct c (Vector.ofFn (fun j => (xs.get j).get i)))) =
      ∑ j : Fin t, bit c j.val • rectDecode n (xs.get j) := by
  ext i k
  simp only [rectDecode, get_ofFn, rectRowProduct, bit_xorList,
    List.map_ofFn, List.sum_ofFn, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  cases h : c.testBit j.val <;> simp [h, bit]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
