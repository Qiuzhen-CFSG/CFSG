module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Transport

/-!
# Membership of the original source combination

Every displayed matrix identity is checked using ordinary kernel reduction.

Source: KernelBound/source/README.md and kernel-restriction.json. Numerical
witnesses are checked by Lean; the generator is not trusted.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

set_option maxRecDepth 10000

attribute [local irreducible] squareBasis testForm topOperator basisTransposes rightProducts linearWords
  testFormWord topOperatorWord alternativeBasisWords weights duals productPairs productWords
  embeddingRows embeddingTransposeRows transportMiddles sourceWord sourceMask sourceMiddle topRight topLinearWord


private theorem source_combination : sourceWord =
    xorList (List.ofFn (fun i : Fin 1221 => if sourceMask.testBit i.val then basisFlat i.val else 0)) := by
  decide +kernel

 theorem source_mem : flatMatrix sourceWord ∈ exteriorFormSpace := by
  rw [source_combination]
  apply flatMatrix_xorList_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split
  · rw [basis_decode]
    exact exteriorBasisForm_mem i
  · rw [flatMatrix_zero]
    exact Submodule.zero_mem _

private theorem source_transport :
    upperBlockLinear (formCoordinatesLinear (flatMatrix sourceWord)) = testForm := by
  rw [restriction_eq, ← embeddingTransposeRows_spec, ← embeddingRows_spec]
  let srcRows : Vector ℕ 112 := Vector.ofFn (fun i => flatRow sourceWord i.val)
  have hs : rowsMatrix srcRows = flatMatrix sourceWord := by
    funext i j
    simp only [rowsMatrix, srcRows, get_ofFn]
    exact flatRow_bit sourceWord i j
  rw [← hs]
  have h1 : ∀ i : Fin 56, rowProduct (embeddingTransposeRows.get i) srcRows = sourceMiddle.get i := by
    simp only [srcRows, rowProduct, get_ofFn]
    decide +kernel
  rw [rows_product_eq embeddingTransposeRows srcRows sourceMiddle h1]
  have h2 : ∀ i : Fin 56, rowProduct (sourceMiddle.get i) embeddingRows = (halfRows testFormWord).get i := by
    simp only [halfRows, get_ofFn]
    decide +kernel
  rw [rows_product_eq sourceMiddle embeddingRows (halfRows testFormWord) h2, halfRows_spec]
  simp only [testForm]

 theorem testForm_mem : testForm ∈ restrictionSpace := by
  exact ⟨formCoordinatesLinear (flatMatrix sourceWord),
    ⟨flatMatrix sourceWord, source_mem, rfl⟩, source_transport⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
