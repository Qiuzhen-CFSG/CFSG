module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.Data
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Packed products for the flag certificates

A row is the XOR of the selected rows of the right factor. The scan proof
follows the generic binary elimination infrastructure in the retained sibling
FiniteAlgebra/Linear.lean. Only packed multiplication and slicing are needed
here; no reconstruction premise or sibling completeness theorem is imported.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
open LinearMembership GeneratorCertificates

def rowScan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ rowScan (x >>> 1) ys

lemma rowScan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    rowScan x (List.ofFn f) =
      xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [rowScan, xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, rowScan, xorList, ih]
    congr 1
    apply congrArg xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

lemma ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : List.ofFn v.get = v.toList := by
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList (Vector.ofFn_getElem (xs := v)))

lemma rowScan_eq {n : ℕ} (x : ℕ) (ys : Vector ℕ n) :
    rowScan x ys.toList = rectRowProduct x ys := by
  rw [← ofFn_get, rowScan_ofFn]
  rfl

def matrixSlices (x : ℕ) : Vector ℕ 50 :=
  Vector.ofFn (fun i => (x >>> (50 * i.val)) % 2 ^ 50)

lemma decode_matrixSlices (x : ℕ) :
    rectDecode 50 (matrixSlices x) =
      fun i j => bit x (50 * i.val + j.val) := by
  funext i j
  simp only [rectDecode, matrixSlices, get_ofFn, bit,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

lemma affineDirection_eq_slices (k : Fin 124) :
    affineDirection k = rectDecode 50 (matrixSlices (affineDirectionRows.get k)) :=
  (decode_matrixSlices _).symm

lemma scalarDirection_eq_slices (k : Fin 2) :
    scalarDirection k = rectDecode 50 (matrixSlices (scalarDirectionRows.get k)) :=
  (decode_matrixSlices _).symm

lemma conjugation_eq_of_products (S : RestrictionMatrix)
    (xs ys zs : Vector ℕ 50)
    (hS : S = rectDecode 50 xs)
    (hleft : ∀ i, rowScan (flagInverseRows.get i) xs.toList = ys.get i)
    (hright : ∀ i, rowScan (ys.get i) flagRows.toList = zs.get i) :
    flagConjugation S = rectDecode 50 zs := by
  change flagInverse * S * flagMatrix = _
  rw [hS, flagInverse, flagMatrix]
  rw [rectProduct_eq flagInverseRows xs ys (fun i => (rowScan_eq _ _).symm.trans (hleft i))]
  exact rectProduct_eq ys flagRows zs (fun i => (rowScan_eq _ _).symm.trans (hright i))

lemma strict_of_row_remainders (ys : Vector ℕ 50)
    (h : ∀ i, ys.get i % 2 ^ (i.val + 1) = 0) :
    ∀ i j : Fin 50, j ≤ i → rectDecode 50 ys i j = 0 := by
  intro i j hj
  have heq := congrArg (fun x : ℕ => x.testBit j.val) (h i)
  have hlt : j.val < i.val + 1 := by omega
  simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and,
    Nat.zero_testBit] at heq
  simp only [rectDecode, bit, heq, Bool.false_eq_true, ↓reduceIte]

lemma direction_strict_of_products (k : Fin 124)
    (ys zs : Vector ℕ 50)
    (hleft : ∀ i, rowScan (flagInverseRows.get i)
      (matrixSlices (affineDirectionRows.get k)).toList = ys.get i)
    (hright : ∀ i, rowScan (ys.get i) flagRows.toList = zs.get i)
    (hstrict : ∀ i, zs.get i % 2 ^ (i.val + 1) = 0) :
    ∀ i j : Fin 50, j ≤ i → flagConjugation (affineDirection k) i j = 0 := by
  rw [conjugation_eq_of_products _ _ ys zs (affineDirection_eq_slices k) hleft hright]
  exact strict_of_row_remainders zs hstrict

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate
