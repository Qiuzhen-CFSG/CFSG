module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Arithmetic

/-!
# Row and sum identities for the local twist annihilator

Source: the actual ATLAS matrices in `Janko4/Model/Data.lean` and the
certified local words in `NormalizerSquares/LocalAction/TwoCoreCentralizer`.
Reproduce with `TwistedCertificate/source/generate_certificate.py`.
All numerical identities are kernel-checked.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
open Janko4.GeneratorCertificates Janko4.Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000 in
theorem even_sum : evenPolynomial = eMatrix :=
  NormalizerSquares.CommutantCertificate.decode_sum_rows evenRows eRows (by decide +kernel)

set_option maxRecDepth 10000 in
theorem odd_sum : oddPolynomial = oMatrix :=
  NormalizerSquares.CommutantCertificate.decode_sum_rows oddRows oRows (by decide +kernel)

set_option maxRecDepth 10000 in
theorem original_sum : eMatrix + oMatrix = rMatrix := by
  have h := NormalizerSquares.CommutantCertificate.decode_sum_rows [eRows, oRows] rRows (by decide +kernel)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  exact h

set_option maxRecDepth 10000 in
theorem twisted_sum : eMatrix + aoMatrix = tMatrix := by
  have h := NormalizerSquares.CommutantCertificate.decode_sum_rows [eRows, aoRows] tRows (by decide +kernel)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  exact h

set_option maxRecDepth 10000 in
theorem target_sum : 1 + matrixA = nMatrix := by
  have h := NormalizerSquares.CommutantCertificate.decode_sum_rows [v000, aRows] nRows (by decide +kernel)
  have he : m000 + aMatrix = nMatrix := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    exact h
  rw [identity_matrix, a_matrix] at he
  exact he

theorem twisted_zero_row : tMatrix 0 = 0 := by
  have h : tRows.get 0 = 0 := by decide +kernel
  funext j
  change bit (tRows.get 0) j.val = 0
  simp [h, bit]

theorem target_nonzero_row : (1 + matrixA : BinaryMatrix) 0 ≠ 0 := by
  intro h
  have he := congrFun h 0
  have hn : (1 + matrixA : BinaryMatrix) 0 0 = 1 := by decide +kernel
  rw [hn] at he
  exact one_ne_zero he

end Janko4.OuterReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate
