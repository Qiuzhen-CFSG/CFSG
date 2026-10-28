module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Output

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem shapes_0 : shapeChunk 0 512 = true := by decide +kernel

theorem shape_range_0 (n : Nat) (hlo : 0 ≤ n) (hhi : n < 512) :
    shapeAt n = true := shapeChunk_sound shapes_0 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_512 : shapeChunk 512 512 = true := by decide +kernel

theorem shape_range_512 (n : Nat) (hlo : 512 ≤ n) (hhi : n < 1024) :
    shapeAt n = true := shapeChunk_sound shapes_512 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_1024 : shapeChunk 1024 512 = true := by decide +kernel

theorem shape_range_1024 (n : Nat) (hlo : 1024 ≤ n) (hhi : n < 1536) :
    shapeAt n = true := shapeChunk_sound shapes_1024 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_1536 : shapeChunk 1536 512 = true := by decide +kernel

theorem shape_range_1536 (n : Nat) (hlo : 1536 ≤ n) (hhi : n < 2048) :
    shapeAt n = true := shapeChunk_sound shapes_1536 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_2048 : shapeChunk 2048 512 = true := by decide +kernel

theorem shape_range_2048 (n : Nat) (hlo : 2048 ≤ n) (hhi : n < 2560) :
    shapeAt n = true := shapeChunk_sound shapes_2048 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_2560 : shapeChunk 2560 512 = true := by decide +kernel

theorem shape_range_2560 (n : Nat) (hlo : 2560 ≤ n) (hhi : n < 3072) :
    shapeAt n = true := shapeChunk_sound shapes_2560 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_3072 : shapeChunk 3072 512 = true := by decide +kernel

theorem shape_range_3072 (n : Nat) (hlo : 3072 ≤ n) (hhi : n < 3584) :
    shapeAt n = true := shapeChunk_sound shapes_3072 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_3584 : shapeChunk 3584 512 = true := by decide +kernel

theorem shape_range_3584 (n : Nat) (hlo : 3584 ≤ n) (hhi : n < 4096) :
    shapeAt n = true := shapeChunk_sound shapes_3584 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_4096 : shapeChunk 4096 512 = true := by decide +kernel

theorem shape_range_4096 (n : Nat) (hlo : 4096 ≤ n) (hhi : n < 4608) :
    shapeAt n = true := shapeChunk_sound shapes_4096 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_4608 : shapeChunk 4608 512 = true := by decide +kernel

theorem shape_range_4608 (n : Nat) (hlo : 4608 ≤ n) (hhi : n < 5120) :
    shapeAt n = true := shapeChunk_sound shapes_4608 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_5120 : shapeChunk 5120 512 = true := by decide +kernel

theorem shape_range_5120 (n : Nat) (hlo : 5120 ≤ n) (hhi : n < 5632) :
    shapeAt n = true := shapeChunk_sound shapes_5120 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_5632 : shapeChunk 5632 512 = true := by decide +kernel

theorem shape_range_5632 (n : Nat) (hlo : 5632 ≤ n) (hhi : n < 6144) :
    shapeAt n = true := shapeChunk_sound shapes_5632 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_6144 : shapeChunk 6144 512 = true := by decide +kernel

theorem shape_range_6144 (n : Nat) (hlo : 6144 ≤ n) (hhi : n < 6656) :
    shapeAt n = true := shapeChunk_sound shapes_6144 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_6656 : shapeChunk 6656 512 = true := by decide +kernel

theorem shape_range_6656 (n : Nat) (hlo : 6656 ≤ n) (hhi : n < 7168) :
    shapeAt n = true := shapeChunk_sound shapes_6656 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_7168 : shapeChunk 7168 512 = true := by decide +kernel

theorem shape_range_7168 (n : Nat) (hlo : 7168 ≤ n) (hhi : n < 7680) :
    shapeAt n = true := shapeChunk_sound shapes_7168 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_7680 : shapeChunk 7680 512 = true := by decide +kernel

theorem shape_range_7680 (n : Nat) (hlo : 7680 ≤ n) (hhi : n < 8192) :
    shapeAt n = true := shapeChunk_sound shapes_7680 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_8192 : shapeChunk 8192 512 = true := by decide +kernel

theorem shape_range_8192 (n : Nat) (hlo : 8192 ≤ n) (hhi : n < 8704) :
    shapeAt n = true := shapeChunk_sound shapes_8192 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_8704 : shapeChunk 8704 512 = true := by decide +kernel

theorem shape_range_8704 (n : Nat) (hlo : 8704 ≤ n) (hhi : n < 9216) :
    shapeAt n = true := shapeChunk_sound shapes_8704 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_9216 : shapeChunk 9216 512 = true := by decide +kernel

theorem shape_range_9216 (n : Nat) (hlo : 9216 ≤ n) (hhi : n < 9728) :
    shapeAt n = true := shapeChunk_sound shapes_9216 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_9728 : shapeChunk 9728 512 = true := by decide +kernel

theorem shape_range_9728 (n : Nat) (hlo : 9728 ≤ n) (hhi : n < 10240) :
    shapeAt n = true := shapeChunk_sound shapes_9728 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_10240 : shapeChunk 10240 512 = true := by decide +kernel

theorem shape_range_10240 (n : Nat) (hlo : 10240 ≤ n) (hhi : n < 10752) :
    shapeAt n = true := shapeChunk_sound shapes_10240 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_10752 : shapeChunk 10752 512 = true := by decide +kernel

theorem shape_range_10752 (n : Nat) (hlo : 10752 ≤ n) (hhi : n < 11264) :
    shapeAt n = true := shapeChunk_sound shapes_10752 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_11264 : shapeChunk 11264 512 = true := by decide +kernel

theorem shape_range_11264 (n : Nat) (hlo : 11264 ≤ n) (hhi : n < 11776) :
    shapeAt n = true := shapeChunk_sound shapes_11264 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_11776 : shapeChunk 11776 512 = true := by decide +kernel

theorem shape_range_11776 (n : Nat) (hlo : 11776 ≤ n) (hhi : n < 12288) :
    shapeAt n = true := shapeChunk_sound shapes_11776 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_12288 : shapeChunk 12288 512 = true := by decide +kernel

theorem shape_range_12288 (n : Nat) (hlo : 12288 ≤ n) (hhi : n < 12800) :
    shapeAt n = true := shapeChunk_sound shapes_12288 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_12800 : shapeChunk 12800 512 = true := by decide +kernel

theorem shape_range_12800 (n : Nat) (hlo : 12800 ≤ n) (hhi : n < 13312) :
    shapeAt n = true := shapeChunk_sound shapes_12800 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_13312 : shapeChunk 13312 512 = true := by decide +kernel

theorem shape_range_13312 (n : Nat) (hlo : 13312 ≤ n) (hhi : n < 13824) :
    shapeAt n = true := shapeChunk_sound shapes_13312 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_13824 : shapeChunk 13824 512 = true := by decide +kernel

theorem shape_range_13824 (n : Nat) (hlo : 13824 ≤ n) (hhi : n < 14336) :
    shapeAt n = true := shapeChunk_sound shapes_13824 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_14336 : shapeChunk 14336 512 = true := by decide +kernel

theorem shape_range_14336 (n : Nat) (hlo : 14336 ≤ n) (hhi : n < 14848) :
    shapeAt n = true := shapeChunk_sound shapes_14336 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_14848 : shapeChunk 14848 512 = true := by decide +kernel

theorem shape_range_14848 (n : Nat) (hlo : 14848 ≤ n) (hhi : n < 15360) :
    shapeAt n = true := shapeChunk_sound shapes_14848 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_15360 : shapeChunk 15360 512 = true := by decide +kernel

theorem shape_range_15360 (n : Nat) (hlo : 15360 ≤ n) (hhi : n < 15872) :
    shapeAt n = true := shapeChunk_sound shapes_15360 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_15872 : shapeChunk 15872 512 = true := by decide +kernel

theorem shape_range_15872 (n : Nat) (hlo : 15872 ≤ n) (hhi : n < 16384) :
    shapeAt n = true := shapeChunk_sound shapes_15872 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_16384 : shapeChunk 16384 512 = true := by decide +kernel

theorem shape_range_16384 (n : Nat) (hlo : 16384 ≤ n) (hhi : n < 16896) :
    shapeAt n = true := shapeChunk_sound shapes_16384 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_16896 : shapeChunk 16896 512 = true := by decide +kernel

theorem shape_range_16896 (n : Nat) (hlo : 16896 ≤ n) (hhi : n < 17408) :
    shapeAt n = true := shapeChunk_sound shapes_16896 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_17408 : shapeChunk 17408 512 = true := by decide +kernel

theorem shape_range_17408 (n : Nat) (hlo : 17408 ≤ n) (hhi : n < 17920) :
    shapeAt n = true := shapeChunk_sound shapes_17408 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_17920 : shapeChunk 17920 512 = true := by decide +kernel

theorem shape_range_17920 (n : Nat) (hlo : 17920 ≤ n) (hhi : n < 18432) :
    shapeAt n = true := shapeChunk_sound shapes_17920 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_18432 : shapeChunk 18432 512 = true := by decide +kernel

theorem shape_range_18432 (n : Nat) (hlo : 18432 ≤ n) (hhi : n < 18944) :
    shapeAt n = true := shapeChunk_sound shapes_18432 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_18944 : shapeChunk 18944 512 = true := by decide +kernel

theorem shape_range_18944 (n : Nat) (hlo : 18944 ≤ n) (hhi : n < 19456) :
    shapeAt n = true := shapeChunk_sound shapes_18944 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_19456 : shapeChunk 19456 512 = true := by decide +kernel

theorem shape_range_19456 (n : Nat) (hlo : 19456 ≤ n) (hhi : n < 19968) :
    shapeAt n = true := shapeChunk_sound shapes_19456 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_19968 : shapeChunk 19968 512 = true := by decide +kernel

theorem shape_range_19968 (n : Nat) (hlo : 19968 ≤ n) (hhi : n < 20480) :
    shapeAt n = true := shapeChunk_sound shapes_19968 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_20480 : shapeChunk 20480 512 = true := by decide +kernel

theorem shape_range_20480 (n : Nat) (hlo : 20480 ≤ n) (hhi : n < 20992) :
    shapeAt n = true := shapeChunk_sound shapes_20480 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_20992 : shapeChunk 20992 512 = true := by decide +kernel

theorem shape_range_20992 (n : Nat) (hlo : 20992 ≤ n) (hhi : n < 21504) :
    shapeAt n = true := shapeChunk_sound shapes_20992 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_21504 : shapeChunk 21504 512 = true := by decide +kernel

theorem shape_range_21504 (n : Nat) (hlo : 21504 ≤ n) (hhi : n < 22016) :
    shapeAt n = true := shapeChunk_sound shapes_21504 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_22016 : shapeChunk 22016 512 = true := by decide +kernel

theorem shape_range_22016 (n : Nat) (hlo : 22016 ≤ n) (hhi : n < 22528) :
    shapeAt n = true := shapeChunk_sound shapes_22016 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_22528 : shapeChunk 22528 512 = true := by decide +kernel

theorem shape_range_22528 (n : Nat) (hlo : 22528 ≤ n) (hhi : n < 23040) :
    shapeAt n = true := shapeChunk_sound shapes_22528 n hlo hhi

set_option maxRecDepth 4096 in
theorem shapes_23040 : shapeChunk 23040 60 = true := by decide +kernel

theorem shape_range_23040 (n : Nat) (hlo : 23040 ≤ n) (hhi : n < 23100) :
    shapeAt n = true := shapeChunk_sound shapes_23040 n hlo hhi

theorem all_shapes (n : Nat) (hn : n < 23100) : shapeAt n = true := by
  by_cases h : n < 11776
  · by_cases h : n < 5632
    · by_cases h : n < 2560
      · by_cases h : n < 1024
        · by_cases h : n < 512
          · exact shape_range_0 n (by omega) (by omega)
          · exact shape_range_512 n (by omega) (by omega)
        · by_cases h : n < 1536
          · exact shape_range_1024 n (by omega) (by omega)
          · by_cases h : n < 2048
            · exact shape_range_1536 n (by omega) (by omega)
            · exact shape_range_2048 n (by omega) (by omega)
      · by_cases h : n < 4096
        · by_cases h : n < 3072
          · exact shape_range_2560 n (by omega) (by omega)
          · by_cases h : n < 3584
            · exact shape_range_3072 n (by omega) (by omega)
            · exact shape_range_3584 n (by omega) (by omega)
        · by_cases h : n < 4608
          · exact shape_range_4096 n (by omega) (by omega)
          · by_cases h : n < 5120
            · exact shape_range_4608 n (by omega) (by omega)
            · exact shape_range_5120 n (by omega) (by omega)
    · by_cases h : n < 8704
      · by_cases h : n < 7168
        · by_cases h : n < 6144
          · exact shape_range_5632 n (by omega) (by omega)
          · by_cases h : n < 6656
            · exact shape_range_6144 n (by omega) (by omega)
            · exact shape_range_6656 n (by omega) (by omega)
        · by_cases h : n < 7680
          · exact shape_range_7168 n (by omega) (by omega)
          · by_cases h : n < 8192
            · exact shape_range_7680 n (by omega) (by omega)
            · exact shape_range_8192 n (by omega) (by omega)
      · by_cases h : n < 10240
        · by_cases h : n < 9216
          · exact shape_range_8704 n (by omega) (by omega)
          · by_cases h : n < 9728
            · exact shape_range_9216 n (by omega) (by omega)
            · exact shape_range_9728 n (by omega) (by omega)
        · by_cases h : n < 10752
          · exact shape_range_10240 n (by omega) (by omega)
          · by_cases h : n < 11264
            · exact shape_range_10752 n (by omega) (by omega)
            · exact shape_range_11264 n (by omega) (by omega)
  · by_cases h : n < 17408
    · by_cases h : n < 14336
      · by_cases h : n < 12800
        · by_cases h : n < 12288
          · exact shape_range_11776 n (by omega) (by omega)
          · exact shape_range_12288 n (by omega) (by omega)
        · by_cases h : n < 13312
          · exact shape_range_12800 n (by omega) (by omega)
          · by_cases h : n < 13824
            · exact shape_range_13312 n (by omega) (by omega)
            · exact shape_range_13824 n (by omega) (by omega)
      · by_cases h : n < 15872
        · by_cases h : n < 14848
          · exact shape_range_14336 n (by omega) (by omega)
          · by_cases h : n < 15360
            · exact shape_range_14848 n (by omega) (by omega)
            · exact shape_range_15360 n (by omega) (by omega)
        · by_cases h : n < 16384
          · exact shape_range_15872 n (by omega) (by omega)
          · by_cases h : n < 16896
            · exact shape_range_16384 n (by omega) (by omega)
            · exact shape_range_16896 n (by omega) (by omega)
    · by_cases h : n < 20480
      · by_cases h : n < 18944
        · by_cases h : n < 17920
          · exact shape_range_17408 n (by omega) (by omega)
          · by_cases h : n < 18432
            · exact shape_range_17920 n (by omega) (by omega)
            · exact shape_range_18432 n (by omega) (by omega)
        · by_cases h : n < 19456
          · exact shape_range_18944 n (by omega) (by omega)
          · by_cases h : n < 19968
            · exact shape_range_19456 n (by omega) (by omega)
            · exact shape_range_19968 n (by omega) (by omega)
      · by_cases h : n < 22016
        · by_cases h : n < 20992
          · exact shape_range_20480 n (by omega) (by omega)
          · by_cases h : n < 21504
            · exact shape_range_20992 n (by omega) (by omega)
            · exact shape_range_21504 n (by omega) (by omega)
        · by_cases h : n < 22528
          · exact shape_range_22016 n (by omega) (by omega)
          · by_cases h : n < 23040
            · exact shape_range_22528 n (by omega) (by omega)
            · exact shape_range_23040 n (by omega) (by omega)

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
