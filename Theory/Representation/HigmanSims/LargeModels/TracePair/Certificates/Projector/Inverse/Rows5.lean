module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Assemble
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.SparseRows

/-!
# HS inverse-product rows 560 through 671

Kernel-checked rows of HT=I+uv for the literal projector witness data.
The eight-row checks run sequentially. This separate compilation unit retains
completed work when later certificate groups are checked. Source and arithmetic
measurements are documented in `../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.InverseRows5
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem block00 :
    checkRows (((hRows.drop 560).take 112).drop 0 |>.take 8) inverseRows (((qRows.drop 560).take 112).drop 0 |>.take 8) = true := by
  apply checkRows_of_sparse 896 [[(365, (1, 0)), (560, (1, 1)), (859, (1, 0))], [(561, (1, 1)), (860, (1, 0)), (861, (1, 0))], [(562, (1, 1)), (862, (1, 0)), (863, (1, 0))], [(367, (1, 0)), (563, (1, 1)), (864, (1, 0))], [(101, (1, 0)), (564, (1, 1)), (865, (1, 0))], [(565, (1, 1)), (866, (1, 0)), (867, (1, 0))], [(369, (1, 0)), (566, (1, 1)), (868, (1, 0))], [(567, (1, 1)), (869, (1, 0)), (870, (1, 0))]] _ _ _ inverseRows_length
  decide +kernel

set_option maxRecDepth 4096 in
private theorem block01 :
    checkRows (((hRows.drop 560).take 112).drop 8 |>.take 8) inverseRows (((qRows.drop 560).take 112).drop 8 |>.take 8) = true := by
  apply checkRows_of_sparse 896 [[(370, (1, 0)), (568, (1, 1)), (871, (1, 0))], [(569, (1, 1)), (872, (1, 0)), (873, (1, 0))], [(570, (1, 1)), (874, (1, 0)), (875, (1, 0))], [(571, (1, 1)), (876, (1, 0)), (877, (1, 0))], [(373, (1, 0)), (572, (1, 1)), (878, (1, 0))], [(573, (1, 1)), (879, (1, 0)), (880, (1, 0))], [(374, (1, 0)), (574, (1, 1)), (881, (1, 0))], [(575, (1, 1)), (882, (1, 0)), (883, (1, 0))]] _ _ _ inverseRows_length
  decide +kernel

set_option maxRecDepth 4096 in
private theorem block02 :
    checkRows (((hRows.drop 560).take 112).drop 16 |>.take 8) inverseRows (((qRows.drop 560).take 112).drop 16 |>.take 8) = true := by
  apply checkRows_of_sparse 896 [[(576, (1, 1)), (884, (1, 0)), (885, (1, 0))], [(376, (1, 0)), (577, (1, 1)), (886, (1, 0))], [(377, (1, 0)), (578, (1, 1)), (887, (1, 0))], [(579, (1, 1)), (888, (1, 0)), (889, (1, 0))], [(580, (1, 1)), (890, (1, 0)), (891, (1, 0))], [(379, (1, 0)), (581, (1, 1)), (892, (1, 0))], [(104, (1, 0)), (582, (1, 1)), (893, (1, 0))], [(583, (1, 1)), (894, (1, 0)), (895, (1, 0))]] _ _ _ inverseRows_length
  decide +kernel

set_option maxRecDepth 4096 in
private theorem block03 :
    checkRows (((hRows.drop 560).take 112).drop 24 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 24 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block04 :
    checkRows (((hRows.drop 560).take 112).drop 32 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 32 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block05 :
    checkRows (((hRows.drop 560).take 112).drop 40 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 40 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block06 :
    checkRows (((hRows.drop 560).take 112).drop 48 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 48 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block07 :
    checkRows (((hRows.drop 560).take 112).drop 56 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 56 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block08 :
    checkRows (((hRows.drop 560).take 112).drop 64 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 64 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block09 :
    checkRows (((hRows.drop 560).take 112).drop 72 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 72 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block10 :
    checkRows (((hRows.drop 560).take 112).drop 80 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 80 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block11 :
    checkRows (((hRows.drop 560).take 112).drop 88 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 88 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block12 :
    checkRows (((hRows.drop 560).take 112).drop 96 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 96 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block13 :
    checkRows (((hRows.drop 560).take 112).drop 104 |>.take 8) inverseRows
      (((qRows.drop 560).take 112).drop 104 |>.take 8) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem checked : checkRows ((hRows.drop 560).take 112) inverseRows ((qRows.drop 560).take 112) = true := by
  have tail112 : checkRows (((hRows.drop 560).take 112).drop 112) inverseRows
      (((qRows.drop 560).take 112).drop 112) = true := by decide +kernel
  have tail104 : checkRows (((hRows.drop 560).take 112).drop 104) inverseRows (((qRows.drop 560).take 112).drop 104) = true :=
    checkRows_drop_split _ _ _ 104 8 block13 tail112
  have tail96 : checkRows (((hRows.drop 560).take 112).drop 96) inverseRows (((qRows.drop 560).take 112).drop 96) = true :=
    checkRows_drop_split _ _ _ 96 8 block12 tail104
  have tail88 : checkRows (((hRows.drop 560).take 112).drop 88) inverseRows (((qRows.drop 560).take 112).drop 88) = true :=
    checkRows_drop_split _ _ _ 88 8 block11 tail96
  have tail80 : checkRows (((hRows.drop 560).take 112).drop 80) inverseRows (((qRows.drop 560).take 112).drop 80) = true :=
    checkRows_drop_split _ _ _ 80 8 block10 tail88
  have tail72 : checkRows (((hRows.drop 560).take 112).drop 72) inverseRows (((qRows.drop 560).take 112).drop 72) = true :=
    checkRows_drop_split _ _ _ 72 8 block09 tail80
  have tail64 : checkRows (((hRows.drop 560).take 112).drop 64) inverseRows (((qRows.drop 560).take 112).drop 64) = true :=
    checkRows_drop_split _ _ _ 64 8 block08 tail72
  have tail56 : checkRows (((hRows.drop 560).take 112).drop 56) inverseRows (((qRows.drop 560).take 112).drop 56) = true :=
    checkRows_drop_split _ _ _ 56 8 block07 tail64
  have tail48 : checkRows (((hRows.drop 560).take 112).drop 48) inverseRows (((qRows.drop 560).take 112).drop 48) = true :=
    checkRows_drop_split _ _ _ 48 8 block06 tail56
  have tail40 : checkRows (((hRows.drop 560).take 112).drop 40) inverseRows (((qRows.drop 560).take 112).drop 40) = true :=
    checkRows_drop_split _ _ _ 40 8 block05 tail48
  have tail32 : checkRows (((hRows.drop 560).take 112).drop 32) inverseRows (((qRows.drop 560).take 112).drop 32) = true :=
    checkRows_drop_split _ _ _ 32 8 block04 tail40
  have tail24 : checkRows (((hRows.drop 560).take 112).drop 24) inverseRows (((qRows.drop 560).take 112).drop 24) = true :=
    checkRows_drop_split _ _ _ 24 8 block03 tail32
  have tail16 : checkRows (((hRows.drop 560).take 112).drop 16) inverseRows (((qRows.drop 560).take 112).drop 16) = true :=
    checkRows_drop_split _ _ _ 16 8 block02 tail24
  have tail8 : checkRows (((hRows.drop 560).take 112).drop 8) inverseRows (((qRows.drop 560).take 112).drop 8) = true :=
    checkRows_drop_split _ _ _ 8 8 block01 tail16
  have tail0 : checkRows (((hRows.drop 560).take 112).drop 0) inverseRows (((qRows.drop 560).take 112).drop 0) = true :=
    checkRows_drop_split _ _ _ 0 8 block00 tail8
  exact tail0

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.InverseRows5
