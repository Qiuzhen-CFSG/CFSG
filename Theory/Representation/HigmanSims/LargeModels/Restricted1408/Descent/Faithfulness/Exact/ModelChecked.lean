module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Model
/-! Kernel certification that the centralizer representatives other than zero
fail to commute with the marked involution on the literal degree-100 carrier.
The witness points and abstract representative comparison are in `Model`. -/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact
set_option Elab.async false
set_option maxRecDepth 4096 in
public theorem model_checked_0 : modelChunk 0 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_128 : modelChunk 128 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_256 : modelChunk 256 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_384 : modelChunk 384 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_512 : modelChunk 512 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_640 : modelChunk 640 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_768 : modelChunk 768 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_896 : modelChunk 896 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1024 : modelChunk 1024 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1152 : modelChunk 1152 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1280 : modelChunk 1280 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1408 : modelChunk 1408 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1536 : modelChunk 1536 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1664 : modelChunk 1664 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1792 : modelChunk 1792 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_1920 : modelChunk 1920 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2048 : modelChunk 2048 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2176 : modelChunk 2176 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2304 : modelChunk 2304 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2432 : modelChunk 2432 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2560 : modelChunk 2560 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2688 : modelChunk 2688 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2816 : modelChunk 2816 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_2944 : modelChunk 2944 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3072 : modelChunk 3072 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3200 : modelChunk 3200 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3328 : modelChunk 3328 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3456 : modelChunk 3456 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3584 : modelChunk 3584 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3712 : modelChunk 3712 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3840 : modelChunk 3840 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_3968 : modelChunk 3968 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4096 : modelChunk 4096 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4224 : modelChunk 4224 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4352 : modelChunk 4352 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4480 : modelChunk 4480 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4608 : modelChunk 4608 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4736 : modelChunk 4736 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4864 : modelChunk 4864 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_4992 : modelChunk 4992 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5120 : modelChunk 5120 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5248 : modelChunk 5248 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5376 : modelChunk 5376 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5504 : modelChunk 5504 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5632 : modelChunk 5632 128 = true := by decide +kernel

set_option maxRecDepth 4096 in
public theorem model_checked_5760 : modelChunk 5760 15 = true := by decide +kernel

public theorem all_modelChecks (n : Nat) (hn : n < 5775) : modelCheck n = true := by
  by_cases h : n < 2944
  · by_cases h : n < 1408
    · by_cases h : n < 640
      · by_cases h : n < 256
        · by_cases h : n < 128
          · exact modelChunk_sound model_checked_0 n (by omega) (by omega)
          · exact modelChunk_sound model_checked_128 n (by omega) (by omega)
        · by_cases h : n < 384
          · exact modelChunk_sound model_checked_256 n (by omega) (by omega)
          · by_cases h : n < 512
            · exact modelChunk_sound model_checked_384 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_512 n (by omega) (by omega)
      · by_cases h : n < 1024
        · by_cases h : n < 768
          · exact modelChunk_sound model_checked_640 n (by omega) (by omega)
          · by_cases h : n < 896
            · exact modelChunk_sound model_checked_768 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_896 n (by omega) (by omega)
        · by_cases h : n < 1152
          · exact modelChunk_sound model_checked_1024 n (by omega) (by omega)
          · by_cases h : n < 1280
            · exact modelChunk_sound model_checked_1152 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_1280 n (by omega) (by omega)
    · by_cases h : n < 2176
      · by_cases h : n < 1792
        · by_cases h : n < 1536
          · exact modelChunk_sound model_checked_1408 n (by omega) (by omega)
          · by_cases h : n < 1664
            · exact modelChunk_sound model_checked_1536 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_1664 n (by omega) (by omega)
        · by_cases h : n < 1920
          · exact modelChunk_sound model_checked_1792 n (by omega) (by omega)
          · by_cases h : n < 2048
            · exact modelChunk_sound model_checked_1920 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_2048 n (by omega) (by omega)
      · by_cases h : n < 2560
        · by_cases h : n < 2304
          · exact modelChunk_sound model_checked_2176 n (by omega) (by omega)
          · by_cases h : n < 2432
            · exact modelChunk_sound model_checked_2304 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_2432 n (by omega) (by omega)
        · by_cases h : n < 2688
          · exact modelChunk_sound model_checked_2560 n (by omega) (by omega)
          · by_cases h : n < 2816
            · exact modelChunk_sound model_checked_2688 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_2816 n (by omega) (by omega)
  · by_cases h : n < 4352
    · by_cases h : n < 3584
      · by_cases h : n < 3200
        · by_cases h : n < 3072
          · exact modelChunk_sound model_checked_2944 n (by omega) (by omega)
          · exact modelChunk_sound model_checked_3072 n (by omega) (by omega)
        · by_cases h : n < 3328
          · exact modelChunk_sound model_checked_3200 n (by omega) (by omega)
          · by_cases h : n < 3456
            · exact modelChunk_sound model_checked_3328 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_3456 n (by omega) (by omega)
      · by_cases h : n < 3968
        · by_cases h : n < 3712
          · exact modelChunk_sound model_checked_3584 n (by omega) (by omega)
          · by_cases h : n < 3840
            · exact modelChunk_sound model_checked_3712 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_3840 n (by omega) (by omega)
        · by_cases h : n < 4096
          · exact modelChunk_sound model_checked_3968 n (by omega) (by omega)
          · by_cases h : n < 4224
            · exact modelChunk_sound model_checked_4096 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_4224 n (by omega) (by omega)
    · by_cases h : n < 5120
      · by_cases h : n < 4736
        · by_cases h : n < 4480
          · exact modelChunk_sound model_checked_4352 n (by omega) (by omega)
          · by_cases h : n < 4608
            · exact modelChunk_sound model_checked_4480 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_4608 n (by omega) (by omega)
        · by_cases h : n < 4864
          · exact modelChunk_sound model_checked_4736 n (by omega) (by omega)
          · by_cases h : n < 4992
            · exact modelChunk_sound model_checked_4864 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_4992 n (by omega) (by omega)
      · by_cases h : n < 5504
        · by_cases h : n < 5248
          · exact modelChunk_sound model_checked_5120 n (by omega) (by omega)
          · by_cases h : n < 5376
            · exact modelChunk_sound model_checked_5248 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_5376 n (by omega) (by omega)
        · by_cases h : n < 5632
          · exact modelChunk_sound model_checked_5504 n (by omega) (by omega)
          · by_cases h : n < 5760
            · exact modelChunk_sound model_checked_5632 n (by omega) (by omega)
            · exact modelChunk_sound model_checked_5760 n (by omega) (by omega)
public theorem representative_eq_one (i : Fin 5775)
    (h : Commute (toCarrier (Cover.definitions.repr certGenerator i.val)) generatorAElement) :
    Cover.definitions.repr certGenerator i.val = 1 := by
  rw [root_of_modelCheck _ (all_modelChecks _ i.isLt) h]
  exact Cover.definitions.repr_zero certGenerator
end Sporadic.LeechRelated.HS.AtlasPresentation.Exact
