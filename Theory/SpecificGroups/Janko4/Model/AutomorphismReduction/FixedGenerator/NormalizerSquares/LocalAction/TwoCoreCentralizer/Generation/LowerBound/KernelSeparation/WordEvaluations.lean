module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.WordProducts0
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.WordProducts1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.WordProducts2
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.Source

/-!
# The factor matrices are the original subgroup words

The first two matrices reuse the evaluated square and seed. Each
subsequent conjugating word appends X or Y to an earlier word;
the certified product identities transfer this recursion to matrices.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

private theorem conjugate_certificate {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ts = packedMul ss rs) :
    toMatrix (g⁻¹ * h * g) = decodeRows ts := by
  have hc' : toMatrix g * decodeRows ts = toMatrix h * toMatrix g := by
    rw [hg, hh, ← decode_packedMul, ← decode_packedMul, hc]
  calc
    toMatrix (g⁻¹ * h * g) = toMatrix g⁻¹ * (toMatrix h * toMatrix g) := by
      simp only [map_mul, mul_assoc]
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ts) := by rw [hc']
    _ = decodeRows ts := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

set_option maxRecDepth 10000 in
private theorem rows_zero : factorRows 0 = tRows := by
  apply Vector.ext
  intro k hk
  change (factorRows 0).get ⟨k, hk⟩ = tRows.get ⟨k, hk⟩
  rw [factorRows, get_ofFn]
  exact (show ∀ k : Fin 112, entry 0 k.val = tRows.get k from by decide +kernel) ⟨k, hk⟩

set_option maxRecDepth 10000 in
private theorem rows_one : factorRows 1 = tp11Rows := by
  apply Vector.ext
  intro k hk
  change (factorRows 1).get ⟨k, hk⟩ = tp11Rows.get ⟨k, hk⟩
  rw [factorRows, get_ofFn]
  exact (show ∀ k : Fin 112, entry 1 k.val = tp11Rows.get k from by decide +kernel) ⟨k, hk⟩

private theorem eval_zero : toMatrix ((kernelFactor 0 : sourceSubgroup) : Model) =
    decodeRows (factorRows 0) := by
  change toMatrix ((sourceSeed ^ 2 : sourceSubgroup) : Model) = _
  rw [coe_sourceSeed_sq, rows_zero]
  exact eval_t

private theorem eval_one : toMatrix ((kernelFactor 1 : sourceSubgroup) : Model) =
    decodeRows (factorRows 1) := by
  change toMatrix ((1⁻¹ * sourceSeed * 1 : sourceSubgroup) : Model) = _
  rw [inv_one, one_mul, mul_one, rows_one]
  change toMatrix (xyxyy ^ 11) = decodeRows tp11Rows
  exact eval_tp11

private theorem eval_2 : toMatrix ((kernelFactor 2 : sourceSubgroup) : Model) =
    decodeRows (factorRows 2) := by
  have h := conjugate_certificate eval_w14 eval_one conjugate_product_2
  convert h using 1
  apply congrArg toMatrix
  change (w14)⁻¹ * (sourceSeed : Model) * (w14) =
    w14⁻¹ * ((1)⁻¹ * (sourceSeed : Model) * (1)) * w14
  group

private theorem eval_3 : toMatrix ((kernelFactor 3 : sourceSubgroup) : Model) =
    decodeRows (factorRows 3) := by
  have h := conjugate_certificate eval_w14 eval_2 conjugate_product_3
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14) =
    w14⁻¹ * ((w14)⁻¹ * (sourceSeed : Model) * (w14)) * w14
  group

private theorem eval_4 : toMatrix ((kernelFactor 4 : sourceSubgroup) : Model) =
    decodeRows (factorRows 4) := by
  have h := conjugate_certificate eval_w10 eval_3 conjugate_product_4
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10) =
    w10⁻¹ * ((w14 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14)) * w10
  group

private theorem eval_5 : toMatrix ((kernelFactor 5 : sourceSubgroup) : Model) =
    decodeRows (factorRows 5) := by
  have h := conjugate_certificate eval_w14 eval_4 conjugate_product_5
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14) =
    w14⁻¹ * ((w14 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10)) * w14
  group

private theorem eval_6 : toMatrix ((kernelFactor 6 : sourceSubgroup) : Model) =
    decodeRows (factorRows 6) := by
  have h := conjugate_certificate eval_w10 eval_5 conjugate_product_6
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10) =
    w10⁻¹ * ((w14 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14)) * w10
  group

private theorem eval_7 : toMatrix ((kernelFactor 7 : sourceSubgroup) : Model) =
    decodeRows (factorRows 7) := by
  have h := conjugate_certificate eval_w14 eval_5 conjugate_product_7
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w14) =
    w14⁻¹ * ((w14 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14)) * w14
  group

private theorem eval_8 : toMatrix ((kernelFactor 8 : sourceSubgroup) : Model) =
    decodeRows (factorRows 8) := by
  have h := conjugate_certificate eval_w14 eval_6 conjugate_product_8
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10 * w14) =
    w14⁻¹ * ((w14 * w14 * w10 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10)) * w14
  group

private theorem eval_9 : toMatrix ((kernelFactor 9 : sourceSubgroup) : Model) =
    decodeRows (factorRows 9) := by
  have h := conjugate_certificate eval_w10 eval_7 conjugate_product_9
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w14 * w10) =
    w10⁻¹ * ((w14 * w14 * w10 * w14 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w14)) * w10
  group

private theorem eval_10 : toMatrix ((kernelFactor 10 : sourceSubgroup) : Model) =
    decodeRows (factorRows 10) := by
  have h := conjugate_certificate eval_w10 eval_8 conjugate_product_10
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w10 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10 * w14 * w10) =
    w10⁻¹ * ((w14 * w14 * w10 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10 * w14)) * w10
  group

private theorem eval_11 : toMatrix ((kernelFactor 11 : sourceSubgroup) : Model) =
    decodeRows (factorRows 11) := by
  have h := conjugate_certificate eval_w14 eval_8 conjugate_product_11
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w10 * w14 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10 * w14 * w14) =
    w14⁻¹ * ((w14 * w14 * w10 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w10 * w14)) * w14
  group

private theorem eval_12 : toMatrix ((kernelFactor 12 : sourceSubgroup) : Model) =
    decodeRows (factorRows 12) := by
  have h := conjugate_certificate eval_w14 eval_9 conjugate_product_12
  convert h using 1
  apply congrArg toMatrix
  change (w14 * w14 * w10 * w14 * w14 * w10 * w14)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w14 * w10 * w14) =
    w14⁻¹ * ((w14 * w14 * w10 * w14 * w14 * w10)⁻¹ * (sourceSeed : Model) * (w14 * w14 * w10 * w14 * w14 * w10)) * w14
  group

theorem eval_factor (n : Fin 13) :
    toMatrix ((kernelFactor n : sourceSubgroup) : Model) = decodeRows (factorRows n) := by
  fin_cases n
  · exact eval_zero
  · exact eval_one
  · exact eval_2
  · exact eval_3
  · exact eval_4
  · exact eval_5
  · exact eval_6
  · exact eval_7
  · exact eval_8
  · exact eval_9
  · exact eval_10
  · exact eval_11
  · exact eval_12

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
