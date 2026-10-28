module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Data
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Rows00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Indexed

/-!
# Checked row operations for the degree-1408 table

These untrusted proposals use fixed row indices and independently validate each
pivot. The pointwise XOR formula is proved in `Indexed.lean`; the following
finite checks use only Lean's kernel. See `source/README.md` in this directory
and the original numerical attribution in `../../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
open PackedBinaryRows.Indexed
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

def initialCheck (i : Nat) : Bool := sRows[i]! == rows0000 i

set_option maxRecDepth 8192 in
private theorem initialChecked0 : checkRange initialCheck 0 384 = true := by
  have c0 : checkRange initialCheck 0 64 = true := by decide +kernel
  have c1 : checkRange initialCheck 64 64 = true := by decide +kernel
  have h1 : checkRange initialCheck 0 128 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 64) (n := 64) c0 c1
  have c2 : checkRange initialCheck 128 64 = true := by decide +kernel
  have h2 : checkRange initialCheck 0 192 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 128) (n := 64) h1 c2
  have c3 : checkRange initialCheck 192 64 = true := by decide +kernel
  have h3 : checkRange initialCheck 0 256 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 192) (n := 64) h2 c3
  have c4 : checkRange initialCheck 256 64 = true := by decide +kernel
  have h4 : checkRange initialCheck 0 320 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 256) (n := 64) h3 c4
  have c5 : checkRange initialCheck 320 64 = true := by decide +kernel
  have h5 : checkRange initialCheck 0 384 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 320) (n := 64) h4 c5
  exact h5

set_option maxRecDepth 8192 in
private theorem initialChecked1 : checkRange initialCheck 384 384 = true := by
  have c6 : checkRange initialCheck 384 64 = true := by decide +kernel
  have c7 : checkRange initialCheck 448 64 = true := by decide +kernel
  have h7 : checkRange initialCheck 384 128 = true :=
    checkRange_append (f := initialCheck) (start := 384) (m := 64) (n := 64) c6 c7
  have c8 : checkRange initialCheck 512 64 = true := by decide +kernel
  have h8 : checkRange initialCheck 384 192 = true :=
    checkRange_append (f := initialCheck) (start := 384) (m := 128) (n := 64) h7 c8
  have c9 : checkRange initialCheck 576 64 = true := by decide +kernel
  have h9 : checkRange initialCheck 384 256 = true :=
    checkRange_append (f := initialCheck) (start := 384) (m := 192) (n := 64) h8 c9
  have c10 : checkRange initialCheck 640 64 = true := by decide +kernel
  have h10 : checkRange initialCheck 384 320 = true :=
    checkRange_append (f := initialCheck) (start := 384) (m := 256) (n := 64) h9 c10
  have c11 : checkRange initialCheck 704 64 = true := by decide +kernel
  have h11 : checkRange initialCheck 384 384 = true :=
    checkRange_append (f := initialCheck) (start := 384) (m := 320) (n := 64) h10 c11
  exact h11

set_option maxRecDepth 8192 in
private theorem initialChecked2 : checkRange initialCheck 768 384 = true := by
  have c12 : checkRange initialCheck 768 64 = true := by decide +kernel
  have c13 : checkRange initialCheck 832 64 = true := by decide +kernel
  have h13 : checkRange initialCheck 768 128 = true :=
    checkRange_append (f := initialCheck) (start := 768) (m := 64) (n := 64) c12 c13
  have c14 : checkRange initialCheck 896 64 = true := by decide +kernel
  have h14 : checkRange initialCheck 768 192 = true :=
    checkRange_append (f := initialCheck) (start := 768) (m := 128) (n := 64) h13 c14
  have c15 : checkRange initialCheck 960 64 = true := by decide +kernel
  have h15 : checkRange initialCheck 768 256 = true :=
    checkRange_append (f := initialCheck) (start := 768) (m := 192) (n := 64) h14 c15
  have c16 : checkRange initialCheck 1024 64 = true := by decide +kernel
  have h16 : checkRange initialCheck 768 320 = true :=
    checkRange_append (f := initialCheck) (start := 768) (m := 256) (n := 64) h15 c16
  have c17 : checkRange initialCheck 1088 64 = true := by decide +kernel
  have h17 : checkRange initialCheck 768 384 = true :=
    checkRange_append (f := initialCheck) (start := 768) (m := 320) (n := 64) h16 c17
  exact h17

set_option maxRecDepth 8192 in
private theorem initialChecked3 : checkRange initialCheck 1152 256 = true := by
  have c18 : checkRange initialCheck 1152 64 = true := by decide +kernel
  have c19 : checkRange initialCheck 1216 64 = true := by decide +kernel
  have h19 : checkRange initialCheck 1152 128 = true :=
    checkRange_append (f := initialCheck) (start := 1152) (m := 64) (n := 64) c18 c19
  have c20 : checkRange initialCheck 1280 64 = true := by decide +kernel
  have h20 : checkRange initialCheck 1152 192 = true :=
    checkRange_append (f := initialCheck) (start := 1152) (m := 128) (n := 64) h19 c20
  have c21 : checkRange initialCheck 1344 64 = true := by decide +kernel
  have h21 : checkRange initialCheck 1152 256 = true :=
    checkRange_append (f := initialCheck) (start := 1152) (m := 192) (n := 64) h20 c21
  exact h21

theorem initialChecked : checkRange initialCheck 0 1408 = true := by
  have h1 : checkRange initialCheck 0 768 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 384) (n := 384) initialChecked0 initialChecked1
  have h2 : checkRange initialCheck 0 1152 = true :=
    checkRange_append (f := initialCheck) (start := 0) (m := 768) (n := 384) h1 initialChecked2
  exact checkRange_append (f := initialCheck) (start := 0) (m := 1152) (n := 256) h2 initialChecked3


end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
