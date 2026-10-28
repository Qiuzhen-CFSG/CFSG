module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.SparseData

/-!
# Kernel-checked sparse inverse products

The first 560 rows of HT=I+uv are checked in blocks of 56, including every
support bound and the equality to the full hRows encoding. This uses the
sound sparse checker, with no matrix identities assumed from the generator.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem block00 :
    checkSparse 896 ((sparseTerms.drop 0).take 56)
      (((hRows.take 560).drop 0).take 56) inverseRows
      (((qRows.take 560).drop 0).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block01 :
    checkSparse 896 ((sparseTerms.drop 56).take 56)
      (((hRows.take 560).drop 56).take 56) inverseRows
      (((qRows.take 560).drop 56).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block02 :
    checkSparse 896 ((sparseTerms.drop 112).take 56)
      (((hRows.take 560).drop 112).take 56) inverseRows
      (((qRows.take 560).drop 112).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block03 :
    checkSparse 896 ((sparseTerms.drop 168).take 56)
      (((hRows.take 560).drop 168).take 56) inverseRows
      (((qRows.take 560).drop 168).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block04 :
    checkSparse 896 ((sparseTerms.drop 224).take 56)
      (((hRows.take 560).drop 224).take 56) inverseRows
      (((qRows.take 560).drop 224).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block05 :
    checkSparse 896 ((sparseTerms.drop 280).take 56)
      (((hRows.take 560).drop 280).take 56) inverseRows
      (((qRows.take 560).drop 280).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block06 :
    checkSparse 896 ((sparseTerms.drop 336).take 56)
      (((hRows.take 560).drop 336).take 56) inverseRows
      (((qRows.take 560).drop 336).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block07 :
    checkSparse 896 ((sparseTerms.drop 392).take 56)
      (((hRows.take 560).drop 392).take 56) inverseRows
      (((qRows.take 560).drop 392).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block08 :
    checkSparse 896 ((sparseTerms.drop 448).take 56)
      (((hRows.take 560).drop 448).take 56) inverseRows
      (((qRows.take 560).drop 448).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem block09 :
    checkSparse 896 ((sparseTerms.drop 504).take 56)
      (((hRows.take 560).drop 504).take 56) inverseRows
      (((qRows.take 560).drop 504).take 56) = true := by decide +kernel

set_option maxRecDepth 4096 in
theorem sparse_checked : checkSparse 896 sparseTerms (hRows.take 560) inverseRows
    (qRows.take 560) = true := by
  have tail560 : checkSparse 896 (sparseTerms.drop 560) ((hRows.take 560).drop 560)
      inverseRows ((qRows.take 560).drop 560) = true := by decide +kernel
  have tail504 : checkSparse 896 (sparseTerms.drop 504) ((hRows.take 560).drop 504)
      inverseRows ((qRows.take 560).drop 504) = true :=
    checkSparse_drop_split 896 _ _ _ _ 504 56 block09 tail560
  have tail448 : checkSparse 896 (sparseTerms.drop 448) ((hRows.take 560).drop 448)
      inverseRows ((qRows.take 560).drop 448) = true :=
    checkSparse_drop_split 896 _ _ _ _ 448 56 block08 tail504
  have tail392 : checkSparse 896 (sparseTerms.drop 392) ((hRows.take 560).drop 392)
      inverseRows ((qRows.take 560).drop 392) = true :=
    checkSparse_drop_split 896 _ _ _ _ 392 56 block07 tail448
  have tail336 : checkSparse 896 (sparseTerms.drop 336) ((hRows.take 560).drop 336)
      inverseRows ((qRows.take 560).drop 336) = true :=
    checkSparse_drop_split 896 _ _ _ _ 336 56 block06 tail392
  have tail280 : checkSparse 896 (sparseTerms.drop 280) ((hRows.take 560).drop 280)
      inverseRows ((qRows.take 560).drop 280) = true :=
    checkSparse_drop_split 896 _ _ _ _ 280 56 block05 tail336
  have tail224 : checkSparse 896 (sparseTerms.drop 224) ((hRows.take 560).drop 224)
      inverseRows ((qRows.take 560).drop 224) = true :=
    checkSparse_drop_split 896 _ _ _ _ 224 56 block04 tail280
  have tail168 : checkSparse 896 (sparseTerms.drop 168) ((hRows.take 560).drop 168)
      inverseRows ((qRows.take 560).drop 168) = true :=
    checkSparse_drop_split 896 _ _ _ _ 168 56 block03 tail224
  have tail112 : checkSparse 896 (sparseTerms.drop 112) ((hRows.take 560).drop 112)
      inverseRows ((qRows.take 560).drop 112) = true :=
    checkSparse_drop_split 896 _ _ _ _ 112 56 block02 tail168
  have tail56 : checkSparse 896 (sparseTerms.drop 56) ((hRows.take 560).drop 56)
      inverseRows ((qRows.take 560).drop 56) = true :=
    checkSparse_drop_split 896 _ _ _ _ 56 56 block01 tail112
  have tail0 : checkSparse 896 (sparseTerms.drop 0) ((hRows.take 560).drop 0)
      inverseRows ((qRows.take 560).drop 0) = true :=
    checkSparse_drop_split 896 _ _ _ _ 0 56 block00 tail56
  exact tail0

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
