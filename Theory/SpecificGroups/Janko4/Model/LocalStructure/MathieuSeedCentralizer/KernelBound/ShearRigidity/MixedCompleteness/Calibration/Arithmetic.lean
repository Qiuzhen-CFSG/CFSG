module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.Arithmetic

/-!
# Transport of all original exterior generators

A certificate decodes an original alternating form and computes the first 56
rows of its two products with the actual shared adapted basis. Submatrix
multiplication transfers these rectangular products to Pᵀ F P. The selected
upper entries and the whole mixed block therefore satisfy Calibration.

Source: ../source/README.md, ../../source/README.md, and
../../../source/README.md. Numerical witnesses are checked separately.
-/

@[expose] public section
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.CalibrationProof
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership FiniteAlgebra

def topTranspose : Vector ℕ 56 :=
  Vector.ofFn (fun a => adaptedTransposeRows.get (Fin.castAdd 56 a))

def Checks (i : Fin 1221) (ambient : Vector ℕ 112) (left top : Vector ℕ 56) : Prop :=
  (∀ a b : Fin 112, (ambient.get a).testBit b.val =
    if a < b then (exteriorFormRows.get i).testBit (exteriorIndex a b)
    else if b < a then (exteriorFormRows.get i).testBit (exteriorIndex b a) else false) ∧
  (∀ a : Fin 56, scan (topTranspose.get a) ambient.toList = left.get a) ∧
  (∀ a : Fin 56, scan (left.get a) adaptedRows.toList = top.get a) ∧
  (∀ t : Fin 595, (evaluationRows.get t).testBit i.val =
    (top.get (upperPositions.get t).1).testBit (upperPositions.get t).2.val) ∧
  (∀ a b : Fin 56, (originalMixedWords.get i).testBit (56 * a.val + b.val) =
    (top.get a).testBit (56 + b.val))

theorem product_of_scan {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (k : ℕ)
    (h : ∀ a, scan (xs.get a) ys.toList = zs.get a) :
    rectDecode n xs * rectDecode k ys = rectDecode k zs := by
  rw [← decode_mulRows]
  congr 1
  apply Vector.ext
  intro a ha
  change (mulRows xs ys).get ⟨a, ha⟩ = zs.get ⟨a, ha⟩
  rw [mulRows, get_ofFn]
  exact h ⟨a, ha⟩

attribute [local irreducible] adaptedRows adaptedTransposeRows exteriorFormRows
  evaluationRows upperPositions originalMixedWords

theorem calibration_of_checks (i : Fin 1221) (ambient : Vector ℕ 112)
    (left top : Vector ℕ 56) (h : Checks i ambient left top) : Calibration i := by
  obtain ⟨ha, hl, ht, hu, hm⟩ := h
  have hamb : rectDecode 112 ambient = exteriorBasisForm i :=
    RadicalCertificate.rectDecode_eq_exterior _ _ ha
  have hleft := product_of_scan topTranspose ambient left 112 hl
  have hprod := product_of_scan left adaptedRows top 112 ht
  have htrans : (decodeRows adaptedTransposeRows).submatrix (Fin.castAdd 56) id =
      rectDecode 112 topTranspose := by
    ext a b
    simp only [rectDecode, topTranspose, get_ofFn, Matrix.submatrix_apply, id_eq,
      decodeRows]
  have partial_mul (M N : BinaryMatrix) :
      (M * N).submatrix (Fin.castAdd 56) id =
        M.submatrix (Fin.castAdd 56) id * N := by
    ext a b
    rfl
  have htop : (adaptedBasisᵀ * exteriorBasisForm i * adaptedBasis).submatrix
      (Fin.castAdd 56) id = rectDecode 112 top := by
    unfold adaptedBasis
    rw [adapted_transpose, ← hamb]
    rw [partial_mul, partial_mul, htrans]
    rw [hleft]
    exact hprod
  constructor
  · intro t
    have hp := congrFun (congrFun htop (upperPositions.get t).1)
      (Fin.castAdd 56 (upperPositions.get t).2)
    change bit (evaluationRows.get t) i.val = _
    change bit (evaluationRows.get t) i.val =
      (adaptedBasisᵀ * exteriorBasisForm i * adaptedBasis)
        (Fin.castAdd 56 (upperPositions.get t).1)
        (Fin.castAdd 56 (upperPositions.get t).2)
    apply Eq.trans ?_ hp.symm
    simp only [rectDecode, bit, Fin.val_castAdd, hu]
  · ext a b
    have hp := congrFun (congrFun htop a) (Fin.natAdd 56 b)
    change bit (originalMixedWords.get i) (56 * a.val + b.val) =
      (adaptedBasisᵀ * exteriorBasisForm i * adaptedBasis)
        (Fin.castAdd 56 a) (Fin.natAdd 56 b)
    apply Eq.trans ?_ hp.symm
    simp only [rectDecode, bit, Fin.val_natAdd, hm]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.CalibrationProof
