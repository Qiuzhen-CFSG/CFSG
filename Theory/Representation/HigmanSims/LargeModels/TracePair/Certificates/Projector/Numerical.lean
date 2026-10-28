module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Inverse.Rows5
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Inverse.Rows6
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Inverse.Rows7
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.SparseChecks

/-!
# Kernel-checked products for the HS null projector

The inverse-row modules prove HT=I+uv. Folded null-column checks use blocks
of 64 to prove Hu=0. The remaining two packed products prove vH=0 and vT=v.
The source witness is `../source/witnesses.json.gz`; its identities are not
trusted until checked here. See `source/README.md` for measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem columnBlock000 :
    checkDots 10 896 uPlanes ((hRows.drop 0).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock001 :
    checkDots 10 896 uPlanes ((hRows.drop 64).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock002 :
    checkDots 10 896 uPlanes ((hRows.drop 128).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock003 :
    checkDots 10 896 uPlanes ((hRows.drop 192).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock004 :
    checkDots 10 896 uPlanes ((hRows.drop 256).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock005 :
    checkDots 10 896 uPlanes ((hRows.drop 320).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock006 :
    checkDots 10 896 uPlanes ((hRows.drop 384).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock007 :
    checkDots 10 896 uPlanes ((hRows.drop 448).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock008 :
    checkDots 10 896 uPlanes ((hRows.drop 512).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock009 :
    checkDots 10 896 uPlanes ((hRows.drop 576).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock010 :
    checkDots 10 896 uPlanes ((hRows.drop 640).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock011 :
    checkDots 10 896 uPlanes ((hRows.drop 704).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock012 :
    checkDots 10 896 uPlanes ((hRows.drop 768).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem columnBlock013 :
    checkDots 10 896 uPlanes ((hRows.drop 832).take 64) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem dense_checked : checkRows (hRows.drop 560) inverseRows (qRows.drop 560) = true := by
  have tail896 : checkRows (hRows.drop 896) inverseRows (qRows.drop 896) = true := by
    decide +kernel
  have tail784 : checkRows (hRows.drop 784) inverseRows (qRows.drop 784) = true :=
    checkRows_drop_split _ _ _ 784 112 InverseRows7.checked tail896
  have tail672 : checkRows (hRows.drop 672) inverseRows (qRows.drop 672) = true :=
    checkRows_drop_split _ _ _ 672 112 InverseRows6.checked tail784
  have tail560 : checkRows (hRows.drop 560) inverseRows (qRows.drop 560) = true :=
    checkRows_drop_split _ _ _ 560 112 InverseRows5.checked tail672
  exact tail560

theorem inverse_checked : Packed.eval 896 hRows * Packed.eval 896 inverseRows = Packed.eval 896 qRows :=
  eval_product_of_sparse_prefix 896 560 sparseTerms hRows inverseRows qRows
    hRows_length inverseRows_length sparse_checked dense_checked

set_option maxRecDepth 4096 in
theorem column_zero_checked : checkDots 10 896 uPlanes hRows = true := by
  have tail896 : checkDots 10 896 uPlanes (hRows.drop 896) = true := by decide +kernel
  have tail832 : checkDots 10 896 uPlanes (hRows.drop 832) = true :=
    checkDots_drop_split _ _ _ _ 832 64 columnBlock013 tail896
  have tail768 : checkDots 10 896 uPlanes (hRows.drop 768) = true :=
    checkDots_drop_split _ _ _ _ 768 64 columnBlock012 tail832
  have tail704 : checkDots 10 896 uPlanes (hRows.drop 704) = true :=
    checkDots_drop_split _ _ _ _ 704 64 columnBlock011 tail768
  have tail640 : checkDots 10 896 uPlanes (hRows.drop 640) = true :=
    checkDots_drop_split _ _ _ _ 640 64 columnBlock010 tail704
  have tail576 : checkDots 10 896 uPlanes (hRows.drop 576) = true :=
    checkDots_drop_split _ _ _ _ 576 64 columnBlock009 tail640
  have tail512 : checkDots 10 896 uPlanes (hRows.drop 512) = true :=
    checkDots_drop_split _ _ _ _ 512 64 columnBlock008 tail576
  have tail448 : checkDots 10 896 uPlanes (hRows.drop 448) = true :=
    checkDots_drop_split _ _ _ _ 448 64 columnBlock007 tail512
  have tail384 : checkDots 10 896 uPlanes (hRows.drop 384) = true :=
    checkDots_drop_split _ _ _ _ 384 64 columnBlock006 tail448
  have tail320 : checkDots 10 896 uPlanes (hRows.drop 320) = true :=
    checkDots_drop_split _ _ _ _ 320 64 columnBlock005 tail384
  have tail256 : checkDots 10 896 uPlanes (hRows.drop 256) = true :=
    checkDots_drop_split _ _ _ _ 256 64 columnBlock004 tail320
  have tail192 : checkDots 10 896 uPlanes (hRows.drop 192) = true :=
    checkDots_drop_split _ _ _ _ 192 64 columnBlock003 tail256
  have tail128 : checkDots 10 896 uPlanes (hRows.drop 128) = true :=
    checkDots_drop_split _ _ _ _ 128 64 columnBlock002 tail192
  have tail64 : checkDots 10 896 uPlanes (hRows.drop 64) = true :=
    checkDots_drop_split _ _ _ _ 64 64 columnBlock001 tail128
  have tail0 : checkDots 10 896 uPlanes (hRows.drop 0) = true :=
    checkDots_drop_split _ _ _ _ 0 64 columnBlock000 tail64
  exact tail0

set_option maxRecDepth 4096 in
theorem row_zero_checked : product vPlanes hRows = (0, 0) := by decide +kernel

set_option maxRecDepth 4096 in
theorem row_inverse_checked : product vPlanes inverseRows = vPlanes := by decide +kernel

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
