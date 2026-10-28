module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Assemble

/-!
# HS inverse-product rows 784 through 895

Kernel-checked rows of HT=I+uv for the literal projector witness data.
The eight-row checks run sequentially. This separate compilation unit retains
completed work when later certificate groups are checked. Source and arithmetic
measurements are documented in `../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.InverseRows7
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem block00 :
    checkRows (((hRows.drop 784).take 112).drop 0 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 0 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block01 :
    checkRows (((hRows.drop 784).take 112).drop 8 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 8 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block02 :
    checkRows (((hRows.drop 784).take 112).drop 16 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 16 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block03 :
    checkRows (((hRows.drop 784).take 112).drop 24 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 24 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block04 :
    checkRows (((hRows.drop 784).take 112).drop 32 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 32 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block05 :
    checkRows (((hRows.drop 784).take 112).drop 40 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 40 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block06 :
    checkRows (((hRows.drop 784).take 112).drop 48 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 48 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block07 :
    checkRows (((hRows.drop 784).take 112).drop 56 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 56 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block08 :
    checkRows (((hRows.drop 784).take 112).drop 64 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 64 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block09 :
    checkRows (((hRows.drop 784).take 112).drop 72 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 72 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block10 :
    checkRows (((hRows.drop 784).take 112).drop 80 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 80 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block11 :
    checkRows (((hRows.drop 784).take 112).drop 88 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 88 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block12 :
    checkRows (((hRows.drop 784).take 112).drop 96 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 96 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block13 :
    checkRows (((hRows.drop 784).take 112).drop 104 |>.take 8) inverseRows
      (((qRows.drop 784).take 112).drop 104 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem checked : checkRows ((hRows.drop 784).take 112) inverseRows ((qRows.drop 784).take 112) = true := by
  have tail112 : checkRows (((hRows.drop 784).take 112).drop 112) inverseRows
      (((qRows.drop 784).take 112).drop 112) = true := by decide +kernel
  have tail104 : checkRows (((hRows.drop 784).take 112).drop 104) inverseRows (((qRows.drop 784).take 112).drop 104) = true :=
    checkRows_drop_split _ _ _ 104 8 block13 tail112
  have tail96 : checkRows (((hRows.drop 784).take 112).drop 96) inverseRows (((qRows.drop 784).take 112).drop 96) = true :=
    checkRows_drop_split _ _ _ 96 8 block12 tail104
  have tail88 : checkRows (((hRows.drop 784).take 112).drop 88) inverseRows (((qRows.drop 784).take 112).drop 88) = true :=
    checkRows_drop_split _ _ _ 88 8 block11 tail96
  have tail80 : checkRows (((hRows.drop 784).take 112).drop 80) inverseRows (((qRows.drop 784).take 112).drop 80) = true :=
    checkRows_drop_split _ _ _ 80 8 block10 tail88
  have tail72 : checkRows (((hRows.drop 784).take 112).drop 72) inverseRows (((qRows.drop 784).take 112).drop 72) = true :=
    checkRows_drop_split _ _ _ 72 8 block09 tail80
  have tail64 : checkRows (((hRows.drop 784).take 112).drop 64) inverseRows (((qRows.drop 784).take 112).drop 64) = true :=
    checkRows_drop_split _ _ _ 64 8 block08 tail72
  have tail56 : checkRows (((hRows.drop 784).take 112).drop 56) inverseRows (((qRows.drop 784).take 112).drop 56) = true :=
    checkRows_drop_split _ _ _ 56 8 block07 tail64
  have tail48 : checkRows (((hRows.drop 784).take 112).drop 48) inverseRows (((qRows.drop 784).take 112).drop 48) = true :=
    checkRows_drop_split _ _ _ 48 8 block06 tail56
  have tail40 : checkRows (((hRows.drop 784).take 112).drop 40) inverseRows (((qRows.drop 784).take 112).drop 40) = true :=
    checkRows_drop_split _ _ _ 40 8 block05 tail48
  have tail32 : checkRows (((hRows.drop 784).take 112).drop 32) inverseRows (((qRows.drop 784).take 112).drop 32) = true :=
    checkRows_drop_split _ _ _ 32 8 block04 tail40
  have tail24 : checkRows (((hRows.drop 784).take 112).drop 24) inverseRows (((qRows.drop 784).take 112).drop 24) = true :=
    checkRows_drop_split _ _ _ 24 8 block03 tail32
  have tail16 : checkRows (((hRows.drop 784).take 112).drop 16) inverseRows (((qRows.drop 784).take 112).drop 16) = true :=
    checkRows_drop_split _ _ _ 16 8 block02 tail24
  have tail8 : checkRows (((hRows.drop 784).take 112).drop 8) inverseRows (((qRows.drop 784).take 112).drop 8) = true :=
    checkRows_drop_split _ _ _ 8 8 block01 tail16
  have tail0 : checkRows (((hRows.drop 784).take 112).drop 0) inverseRows (((qRows.drop 784).take 112).drop 0) = true :=
    checkRows_drop_split _ _ _ 0 8 block00 tail8
  exact tail0

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.InverseRows7
