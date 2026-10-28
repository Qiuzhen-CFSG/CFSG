module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Data

/-!
# Kernel certificates for the shared long-word products

All checks are ordinary kernel reductions of natural-number equalities.
The representative full product used about 3.5 GiB peak RSS; disable declaration
parallelism here to keep the complete certificate within that measured budget.
The compiler's thread count is unchanged. See `source/README.md`.
-/

set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked

theorem certificate4 : ProductCertificate aRows bRows rows4 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate5 : ProductCertificate rows4 rows4 rows5 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate6 : ProductCertificate aRows inverseRows rows6 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate7 : ProductCertificate rows4 bRows rows7 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate8 : ProductCertificate rows6 inverseRows rows8 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate9 : ProductCertificate rows5 rows7 rows9 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate10 : ProductCertificate rows8 rows8 rows10 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate11 : ProductCertificate rows5 bRows rows11 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate12 : ProductCertificate rows9 rows6 rows12 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate13 : ProductCertificate rows6 rows7 rows13 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate14 : ProductCertificate rows5 rows6 rows14 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate15 : ProductCertificate rows12 rows8 rows15 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate16 : ProductCertificate rows10 rows7 rows16 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate17 : ProductCertificate rows9 rows7 rows17 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate18 : ProductCertificate rows15 rows14 rows18 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate19 : ProductCertificate rows15 rows13 rows19 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate20 : ProductCertificate rows19 rows5 rows20 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate21 : ProductCertificate rows20 rows10 rows21 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate22 : ProductCertificate rows21 rows10 identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem certificate23 : ProductCertificate rows11 rows16 rows23 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate24 : ProductCertificate rows23 rows16 rows24 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate25 : ProductCertificate rows24 rows11 rows25 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate26 : ProductCertificate rows25 rows13 rows26 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate27 : ProductCertificate rows26 rows13 identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem certificate28 : ProductCertificate rows17 rows4 rows28 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate29 : ProductCertificate rows28 rows6 rows29 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate30 : ProductCertificate rows29 rows6 rows30 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate31 : ProductCertificate rows30 rows11 rows31 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate32 : ProductCertificate rows31 rows7 rows32 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate33 : ProductCertificate rows32 rows5 rows33 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate34 : ProductCertificate rows33 rows8 rows34 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate35 : ProductCertificate rows34 rows6 rows35 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate36 : ProductCertificate rows35 rows8 identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem certificate37 : ProductCertificate rows18 rows18 identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem certificate38 : ProductCertificate rows9 rows9 rows38 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate39 : ProductCertificate rows38 rows14 rows39 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate40 : ProductCertificate rows39 rows17 rows40 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate41 : ProductCertificate rows40 rows7 rows41 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate42 : ProductCertificate rows41 rows14 identityRows := by
  unfold ProductCertificate
  decide +kernel

theorem certificate43 : ProductCertificate rows9 rows11 rows43 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate44 : ProductCertificate rows43 rows11 rows44 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate45 : ProductCertificate rows44 rows12 rows45 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate46 : ProductCertificate rows45 rows4 rows46 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate47 : ProductCertificate rows46 rows8 rows47 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate48 : ProductCertificate rows47 rows4 rows48 := by
  unfold ProductCertificate
  decide +kernel

theorem certificate49 : ProductCertificate rows48 rows13 identityRows := by
  unfold ProductCertificate
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked
