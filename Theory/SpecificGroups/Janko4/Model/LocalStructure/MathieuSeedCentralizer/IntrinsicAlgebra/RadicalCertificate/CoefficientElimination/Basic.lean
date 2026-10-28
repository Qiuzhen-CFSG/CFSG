module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.RawSpace
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.Basis

/-!
# Packed arithmetic for the exhaustive raw radical calculation

Sequential XOR products are interpreted as ordinary rectangular binary matrix
products. The other bridge interprets a packed row product as a row of Kᵀ R,
using the checked full-matrix encoding of the original exterior family.
See `source/README.md` for the certificate and its coordinate conventions.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open ExteriorInvariance
namespace CoefficientElimination

/-- Sequential XOR scan: only its proved binary interpretation is used. -/
def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ scan (x >>> 1) ys

private theorem scan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    scan x (List.ofFn f) = GeneratorCertificates.xorList
      (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [scan, GeneratorCertificates.xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, scan, GeneratorCertificates.xorList, ih]
    congr 1
    apply congrArg GeneratorCertificates.xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

def rows {m : ℕ} (n : ℕ) (v : Vector ℕ m) :
    Matrix (Fin m) (Fin n) (ZMod 2) := fun i j => bit (v.get i) j.val

private theorem bit_scan {n : ℕ} (x : ℕ) (v : Vector ℕ n) (j : ℕ) :
    bit (scan x v.toList) j = ∑ k : Fin n, bit x k.val * bit (v.get k) j := by
  have hv : List.ofFn v.get = v.toList :=
    Vector.toList_ofFn.symm.trans (congrArg Vector.toList
      (show Vector.ofFn v.get = v from Vector.ofFn_getElem))
  rw [← hv, scan_ofFn]
  change GeneratorCertificates.bit _ _ = _
  rw [GeneratorCertificates.bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  cases h : x.testBit k.val <;> simp [h, bit, GeneratorCertificates.bit]

theorem rows_mul {m n k : ℕ} (x : Vector ℕ m) (y : Vector ℕ n)
    (z : Vector ℕ m) (h : ∀ i, scan (x.get i) y.toList = z.get i) :
    rows n x * rows k y = rows k z := by
  ext i j
  rw [Matrix.mul_apply]
  exact (bit_scan (x.get i) y j.val).symm.trans (congrArg (fun v => bit v j.val) (h i))

/-- Interpret a packed product by one of the actual saved kernel columns. -/
theorem kernel_row_bit (x : ℕ) (r : Fin 56) (j : Fin 112) :
    bit (flatMulRow (adaptedColumns.get (firstIndex r)) x) j.val =
      (kernelColumnsᵀ * flatMatrix x) r j := by
  change GeneratorCertificates.bit _ _ = _
  rw [flatMulRow, GeneratorCertificates.bit_xorList, List.map_ofFn,
    List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← flatRow_bit x k j]
  change _ = bit (adaptedColumns.get (firstIndex r)) k.val * _
  cases h : (adaptedColumns.get (firstIndex r)).testBit k.val <;>
    simp [h, bit, GeneratorCertificates.bit]

end CoefficientElimination
end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
