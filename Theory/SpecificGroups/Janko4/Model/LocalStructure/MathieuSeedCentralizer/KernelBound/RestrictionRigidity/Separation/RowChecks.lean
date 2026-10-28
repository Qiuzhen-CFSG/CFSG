module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Data

/-!
# Calibration of the actual basis and linear terms

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

theorem transposeRows_of_check {m n : ℕ} (a : Vector ℕ m) (b : Vector ℕ n)
    (h : ∀ i : Fin n, b.get i = xorList (List.ofFn (fun j : Fin m =>
      if (a.get j).testBit i.val then 2^j.val else 0))) :
    rowsMatrix (n := m) b = (rowsMatrix (n := n) a)ᵀ := by
  rw [← rowsMatrix_transpose]
  congr 1
  apply Vector.ext
  intro i hi
  change b.get ⟨i,hi⟩ = (rowsTranspose n a).get ⟨i,hi⟩
  rw [rowsTranspose, get_ofFn]
  exact h ⟨i,hi⟩

theorem addRows_of_check {m n : ℕ} (a b c : Vector ℕ m)
    (h : ∀ i : Fin m, c.get i = a.get i ^^^ b.get i) :
    rowsMatrix (n := n) c = rowsMatrix a + rowsMatrix b := by
  funext i j
  change bit (c.get i) j.val = bit (a.get i) j.val + bit (b.get i) j.val
  rw [h, bit_xor]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
