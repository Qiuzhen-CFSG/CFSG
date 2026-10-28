module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Bound.LocalFinite.Shapes04

/-! Kernel checks for the conditional local coset certificate.
Each accepted step is an actual word deduction. The four relator identities
remain explicit premises; see `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
open Subgroup.CosetWordCertificate

theorem all_hold (hr : ∀ r : Fin 4, eval subgroupGenerator (extraRelatorWord r) = 1) :
    ∀ n, n < 54221 → Holds smallSubgroup subgroupGenerator (definitions.repr subgroupGenerator) (facts n) := holds_54221 hr

theorem shape_all (n : Nat) (hn : n < 20160) : shapeAt n = true := by
  by_cases h10112 : n < 10112
  ·
    by_cases h4992 : n < 4992
    ·
      by_cases h2432 : n < 2432
      ·
        by_cases h1152 : n < 1152
        ·
          by_cases h512 : n < 512
          ·
            by_cases h256 : n < 256
            ·
              by_cases h128 : n < 128
              ·
                exact shapeBlock_spec 0 128 shape_checked_0 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 128 128 shape_checked_128 n (by omega) (by omega)
            ·
              by_cases h384 : n < 384
              ·
                exact shapeBlock_spec 256 128 shape_checked_256 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 384 128 shape_checked_384 n (by omega) (by omega)
          ·
            by_cases h768 : n < 768
            ·
              by_cases h640 : n < 640
              ·
                exact shapeBlock_spec 512 128 shape_checked_512 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 640 128 shape_checked_640 n (by omega) (by omega)
            ·
              by_cases h896 : n < 896
              ·
                exact shapeBlock_spec 768 128 shape_checked_768 n (by omega) (by omega)
              ·
                by_cases h1024 : n < 1024
                ·
                  exact shapeBlock_spec 896 128 shape_checked_896 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 1024 128 shape_checked_1024 n (by omega) (by omega)
        ·
          by_cases h1792 : n < 1792
          ·
            by_cases h1408 : n < 1408
            ·
              by_cases h1280 : n < 1280
              ·
                exact shapeBlock_spec 1152 128 shape_checked_1152 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 1280 128 shape_checked_1280 n (by omega) (by omega)
            ·
              by_cases h1536 : n < 1536
              ·
                exact shapeBlock_spec 1408 128 shape_checked_1408 n (by omega) (by omega)
              ·
                by_cases h1664 : n < 1664
                ·
                  exact shapeBlock_spec 1536 128 shape_checked_1536 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 1664 128 shape_checked_1664 n (by omega) (by omega)
          ·
            by_cases h2048 : n < 2048
            ·
              by_cases h1920 : n < 1920
              ·
                exact shapeBlock_spec 1792 128 shape_checked_1792 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 1920 128 shape_checked_1920 n (by omega) (by omega)
            ·
              by_cases h2176 : n < 2176
              ·
                exact shapeBlock_spec 2048 128 shape_checked_2048 n (by omega) (by omega)
              ·
                by_cases h2304 : n < 2304
                ·
                  exact shapeBlock_spec 2176 128 shape_checked_2176 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 2304 128 shape_checked_2304 n (by omega) (by omega)
      ·
        by_cases h3712 : n < 3712
        ·
          by_cases h3072 : n < 3072
          ·
            by_cases h2688 : n < 2688
            ·
              by_cases h2560 : n < 2560
              ·
                exact shapeBlock_spec 2432 128 shape_checked_2432 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 2560 128 shape_checked_2560 n (by omega) (by omega)
            ·
              by_cases h2816 : n < 2816
              ·
                exact shapeBlock_spec 2688 128 shape_checked_2688 n (by omega) (by omega)
              ·
                by_cases h2944 : n < 2944
                ·
                  exact shapeBlock_spec 2816 128 shape_checked_2816 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 2944 128 shape_checked_2944 n (by omega) (by omega)
          ·
            by_cases h3328 : n < 3328
            ·
              by_cases h3200 : n < 3200
              ·
                exact shapeBlock_spec 3072 128 shape_checked_3072 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 3200 128 shape_checked_3200 n (by omega) (by omega)
            ·
              by_cases h3456 : n < 3456
              ·
                exact shapeBlock_spec 3328 128 shape_checked_3328 n (by omega) (by omega)
              ·
                by_cases h3584 : n < 3584
                ·
                  exact shapeBlock_spec 3456 128 shape_checked_3456 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 3584 128 shape_checked_3584 n (by omega) (by omega)
        ·
          by_cases h4352 : n < 4352
          ·
            by_cases h3968 : n < 3968
            ·
              by_cases h3840 : n < 3840
              ·
                exact shapeBlock_spec 3712 128 shape_checked_3712 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 3840 128 shape_checked_3840 n (by omega) (by omega)
            ·
              by_cases h4096 : n < 4096
              ·
                exact shapeBlock_spec 3968 128 shape_checked_3968 n (by omega) (by omega)
              ·
                by_cases h4224 : n < 4224
                ·
                  exact shapeBlock_spec 4096 128 shape_checked_4096 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 4224 128 shape_checked_4224 n (by omega) (by omega)
          ·
            by_cases h4608 : n < 4608
            ·
              by_cases h4480 : n < 4480
              ·
                exact shapeBlock_spec 4352 128 shape_checked_4352 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 4480 128 shape_checked_4480 n (by omega) (by omega)
            ·
              by_cases h4736 : n < 4736
              ·
                exact shapeBlock_spec 4608 128 shape_checked_4608 n (by omega) (by omega)
              ·
                by_cases h4864 : n < 4864
                ·
                  exact shapeBlock_spec 4736 128 shape_checked_4736 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 4864 128 shape_checked_4864 n (by omega) (by omega)
    ·
      by_cases h7552 : n < 7552
      ·
        by_cases h6272 : n < 6272
        ·
          by_cases h5632 : n < 5632
          ·
            by_cases h5248 : n < 5248
            ·
              by_cases h5120 : n < 5120
              ·
                exact shapeBlock_spec 4992 128 shape_checked_4992 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 5120 128 shape_checked_5120 n (by omega) (by omega)
            ·
              by_cases h5376 : n < 5376
              ·
                exact shapeBlock_spec 5248 128 shape_checked_5248 n (by omega) (by omega)
              ·
                by_cases h5504 : n < 5504
                ·
                  exact shapeBlock_spec 5376 128 shape_checked_5376 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 5504 128 shape_checked_5504 n (by omega) (by omega)
          ·
            by_cases h5888 : n < 5888
            ·
              by_cases h5760 : n < 5760
              ·
                exact shapeBlock_spec 5632 128 shape_checked_5632 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 5760 128 shape_checked_5760 n (by omega) (by omega)
            ·
              by_cases h6016 : n < 6016
              ·
                exact shapeBlock_spec 5888 128 shape_checked_5888 n (by omega) (by omega)
              ·
                by_cases h6144 : n < 6144
                ·
                  exact shapeBlock_spec 6016 128 shape_checked_6016 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 6144 128 shape_checked_6144 n (by omega) (by omega)
        ·
          by_cases h6912 : n < 6912
          ·
            by_cases h6528 : n < 6528
            ·
              by_cases h6400 : n < 6400
              ·
                exact shapeBlock_spec 6272 128 shape_checked_6272 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 6400 128 shape_checked_6400 n (by omega) (by omega)
            ·
              by_cases h6656 : n < 6656
              ·
                exact shapeBlock_spec 6528 128 shape_checked_6528 n (by omega) (by omega)
              ·
                by_cases h6784 : n < 6784
                ·
                  exact shapeBlock_spec 6656 128 shape_checked_6656 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 6784 128 shape_checked_6784 n (by omega) (by omega)
          ·
            by_cases h7168 : n < 7168
            ·
              by_cases h7040 : n < 7040
              ·
                exact shapeBlock_spec 6912 128 shape_checked_6912 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 7040 128 shape_checked_7040 n (by omega) (by omega)
            ·
              by_cases h7296 : n < 7296
              ·
                exact shapeBlock_spec 7168 128 shape_checked_7168 n (by omega) (by omega)
              ·
                by_cases h7424 : n < 7424
                ·
                  exact shapeBlock_spec 7296 128 shape_checked_7296 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 7424 128 shape_checked_7424 n (by omega) (by omega)
      ·
        by_cases h8832 : n < 8832
        ·
          by_cases h8192 : n < 8192
          ·
            by_cases h7808 : n < 7808
            ·
              by_cases h7680 : n < 7680
              ·
                exact shapeBlock_spec 7552 128 shape_checked_7552 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 7680 128 shape_checked_7680 n (by omega) (by omega)
            ·
              by_cases h7936 : n < 7936
              ·
                exact shapeBlock_spec 7808 128 shape_checked_7808 n (by omega) (by omega)
              ·
                by_cases h8064 : n < 8064
                ·
                  exact shapeBlock_spec 7936 128 shape_checked_7936 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 8064 128 shape_checked_8064 n (by omega) (by omega)
          ·
            by_cases h8448 : n < 8448
            ·
              by_cases h8320 : n < 8320
              ·
                exact shapeBlock_spec 8192 128 shape_checked_8192 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 8320 128 shape_checked_8320 n (by omega) (by omega)
            ·
              by_cases h8576 : n < 8576
              ·
                exact shapeBlock_spec 8448 128 shape_checked_8448 n (by omega) (by omega)
              ·
                by_cases h8704 : n < 8704
                ·
                  exact shapeBlock_spec 8576 128 shape_checked_8576 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 8704 128 shape_checked_8704 n (by omega) (by omega)
        ·
          by_cases h9472 : n < 9472
          ·
            by_cases h9088 : n < 9088
            ·
              by_cases h8960 : n < 8960
              ·
                exact shapeBlock_spec 8832 128 shape_checked_8832 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 8960 128 shape_checked_8960 n (by omega) (by omega)
            ·
              by_cases h9216 : n < 9216
              ·
                exact shapeBlock_spec 9088 128 shape_checked_9088 n (by omega) (by omega)
              ·
                by_cases h9344 : n < 9344
                ·
                  exact shapeBlock_spec 9216 128 shape_checked_9216 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 9344 128 shape_checked_9344 n (by omega) (by omega)
          ·
            by_cases h9728 : n < 9728
            ·
              by_cases h9600 : n < 9600
              ·
                exact shapeBlock_spec 9472 128 shape_checked_9472 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 9600 128 shape_checked_9600 n (by omega) (by omega)
            ·
              by_cases h9856 : n < 9856
              ·
                exact shapeBlock_spec 9728 128 shape_checked_9728 n (by omega) (by omega)
              ·
                by_cases h9984 : n < 9984
                ·
                  exact shapeBlock_spec 9856 128 shape_checked_9856 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 9984 128 shape_checked_9984 n (by omega) (by omega)
  ·
    by_cases h15104 : n < 15104
    ·
      by_cases h12544 : n < 12544
      ·
        by_cases h11264 : n < 11264
        ·
          by_cases h10624 : n < 10624
          ·
            by_cases h10368 : n < 10368
            ·
              by_cases h10240 : n < 10240
              ·
                exact shapeBlock_spec 10112 128 shape_checked_10112 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 10240 128 shape_checked_10240 n (by omega) (by omega)
            ·
              by_cases h10496 : n < 10496
              ·
                exact shapeBlock_spec 10368 128 shape_checked_10368 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 10496 128 shape_checked_10496 n (by omega) (by omega)
          ·
            by_cases h10880 : n < 10880
            ·
              by_cases h10752 : n < 10752
              ·
                exact shapeBlock_spec 10624 128 shape_checked_10624 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 10752 128 shape_checked_10752 n (by omega) (by omega)
            ·
              by_cases h11008 : n < 11008
              ·
                exact shapeBlock_spec 10880 128 shape_checked_10880 n (by omega) (by omega)
              ·
                by_cases h11136 : n < 11136
                ·
                  exact shapeBlock_spec 11008 128 shape_checked_11008 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 11136 128 shape_checked_11136 n (by omega) (by omega)
        ·
          by_cases h11904 : n < 11904
          ·
            by_cases h11520 : n < 11520
            ·
              by_cases h11392 : n < 11392
              ·
                exact shapeBlock_spec 11264 128 shape_checked_11264 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 11392 128 shape_checked_11392 n (by omega) (by omega)
            ·
              by_cases h11648 : n < 11648
              ·
                exact shapeBlock_spec 11520 128 shape_checked_11520 n (by omega) (by omega)
              ·
                by_cases h11776 : n < 11776
                ·
                  exact shapeBlock_spec 11648 128 shape_checked_11648 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 11776 128 shape_checked_11776 n (by omega) (by omega)
          ·
            by_cases h12160 : n < 12160
            ·
              by_cases h12032 : n < 12032
              ·
                exact shapeBlock_spec 11904 128 shape_checked_11904 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 12032 128 shape_checked_12032 n (by omega) (by omega)
            ·
              by_cases h12288 : n < 12288
              ·
                exact shapeBlock_spec 12160 128 shape_checked_12160 n (by omega) (by omega)
              ·
                by_cases h12416 : n < 12416
                ·
                  exact shapeBlock_spec 12288 128 shape_checked_12288 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 12416 128 shape_checked_12416 n (by omega) (by omega)
      ·
        by_cases h13824 : n < 13824
        ·
          by_cases h13184 : n < 13184
          ·
            by_cases h12800 : n < 12800
            ·
              by_cases h12672 : n < 12672
              ·
                exact shapeBlock_spec 12544 128 shape_checked_12544 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 12672 128 shape_checked_12672 n (by omega) (by omega)
            ·
              by_cases h12928 : n < 12928
              ·
                exact shapeBlock_spec 12800 128 shape_checked_12800 n (by omega) (by omega)
              ·
                by_cases h13056 : n < 13056
                ·
                  exact shapeBlock_spec 12928 128 shape_checked_12928 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 13056 128 shape_checked_13056 n (by omega) (by omega)
          ·
            by_cases h13440 : n < 13440
            ·
              by_cases h13312 : n < 13312
              ·
                exact shapeBlock_spec 13184 128 shape_checked_13184 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 13312 128 shape_checked_13312 n (by omega) (by omega)
            ·
              by_cases h13568 : n < 13568
              ·
                exact shapeBlock_spec 13440 128 shape_checked_13440 n (by omega) (by omega)
              ·
                by_cases h13696 : n < 13696
                ·
                  exact shapeBlock_spec 13568 128 shape_checked_13568 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 13696 128 shape_checked_13696 n (by omega) (by omega)
        ·
          by_cases h14464 : n < 14464
          ·
            by_cases h14080 : n < 14080
            ·
              by_cases h13952 : n < 13952
              ·
                exact shapeBlock_spec 13824 128 shape_checked_13824 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 13952 128 shape_checked_13952 n (by omega) (by omega)
            ·
              by_cases h14208 : n < 14208
              ·
                exact shapeBlock_spec 14080 128 shape_checked_14080 n (by omega) (by omega)
              ·
                by_cases h14336 : n < 14336
                ·
                  exact shapeBlock_spec 14208 128 shape_checked_14208 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 14336 128 shape_checked_14336 n (by omega) (by omega)
          ·
            by_cases h14720 : n < 14720
            ·
              by_cases h14592 : n < 14592
              ·
                exact shapeBlock_spec 14464 128 shape_checked_14464 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 14592 128 shape_checked_14592 n (by omega) (by omega)
            ·
              by_cases h14848 : n < 14848
              ·
                exact shapeBlock_spec 14720 128 shape_checked_14720 n (by omega) (by omega)
              ·
                by_cases h14976 : n < 14976
                ·
                  exact shapeBlock_spec 14848 128 shape_checked_14848 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 14976 128 shape_checked_14976 n (by omega) (by omega)
    ·
      by_cases h17664 : n < 17664
      ·
        by_cases h16384 : n < 16384
        ·
          by_cases h15744 : n < 15744
          ·
            by_cases h15360 : n < 15360
            ·
              by_cases h15232 : n < 15232
              ·
                exact shapeBlock_spec 15104 128 shape_checked_15104 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 15232 128 shape_checked_15232 n (by omega) (by omega)
            ·
              by_cases h15488 : n < 15488
              ·
                exact shapeBlock_spec 15360 128 shape_checked_15360 n (by omega) (by omega)
              ·
                by_cases h15616 : n < 15616
                ·
                  exact shapeBlock_spec 15488 128 shape_checked_15488 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 15616 128 shape_checked_15616 n (by omega) (by omega)
          ·
            by_cases h16000 : n < 16000
            ·
              by_cases h15872 : n < 15872
              ·
                exact shapeBlock_spec 15744 128 shape_checked_15744 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 15872 128 shape_checked_15872 n (by omega) (by omega)
            ·
              by_cases h16128 : n < 16128
              ·
                exact shapeBlock_spec 16000 128 shape_checked_16000 n (by omega) (by omega)
              ·
                by_cases h16256 : n < 16256
                ·
                  exact shapeBlock_spec 16128 128 shape_checked_16128 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 16256 128 shape_checked_16256 n (by omega) (by omega)
        ·
          by_cases h17024 : n < 17024
          ·
            by_cases h16640 : n < 16640
            ·
              by_cases h16512 : n < 16512
              ·
                exact shapeBlock_spec 16384 128 shape_checked_16384 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 16512 128 shape_checked_16512 n (by omega) (by omega)
            ·
              by_cases h16768 : n < 16768
              ·
                exact shapeBlock_spec 16640 128 shape_checked_16640 n (by omega) (by omega)
              ·
                by_cases h16896 : n < 16896
                ·
                  exact shapeBlock_spec 16768 128 shape_checked_16768 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 16896 128 shape_checked_16896 n (by omega) (by omega)
          ·
            by_cases h17280 : n < 17280
            ·
              by_cases h17152 : n < 17152
              ·
                exact shapeBlock_spec 17024 128 shape_checked_17024 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 17152 128 shape_checked_17152 n (by omega) (by omega)
            ·
              by_cases h17408 : n < 17408
              ·
                exact shapeBlock_spec 17280 128 shape_checked_17280 n (by omega) (by omega)
              ·
                by_cases h17536 : n < 17536
                ·
                  exact shapeBlock_spec 17408 128 shape_checked_17408 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 17536 128 shape_checked_17536 n (by omega) (by omega)
      ·
        by_cases h18944 : n < 18944
        ·
          by_cases h18304 : n < 18304
          ·
            by_cases h17920 : n < 17920
            ·
              by_cases h17792 : n < 17792
              ·
                exact shapeBlock_spec 17664 128 shape_checked_17664 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 17792 128 shape_checked_17792 n (by omega) (by omega)
            ·
              by_cases h18048 : n < 18048
              ·
                exact shapeBlock_spec 17920 128 shape_checked_17920 n (by omega) (by omega)
              ·
                by_cases h18176 : n < 18176
                ·
                  exact shapeBlock_spec 18048 128 shape_checked_18048 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 18176 128 shape_checked_18176 n (by omega) (by omega)
          ·
            by_cases h18560 : n < 18560
            ·
              by_cases h18432 : n < 18432
              ·
                exact shapeBlock_spec 18304 128 shape_checked_18304 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 18432 128 shape_checked_18432 n (by omega) (by omega)
            ·
              by_cases h18688 : n < 18688
              ·
                exact shapeBlock_spec 18560 128 shape_checked_18560 n (by omega) (by omega)
              ·
                by_cases h18816 : n < 18816
                ·
                  exact shapeBlock_spec 18688 128 shape_checked_18688 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 18816 128 shape_checked_18816 n (by omega) (by omega)
        ·
          by_cases h19584 : n < 19584
          ·
            by_cases h19200 : n < 19200
            ·
              by_cases h19072 : n < 19072
              ·
                exact shapeBlock_spec 18944 128 shape_checked_18944 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 19072 128 shape_checked_19072 n (by omega) (by omega)
            ·
              by_cases h19328 : n < 19328
              ·
                exact shapeBlock_spec 19200 128 shape_checked_19200 n (by omega) (by omega)
              ·
                by_cases h19456 : n < 19456
                ·
                  exact shapeBlock_spec 19328 128 shape_checked_19328 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 19456 128 shape_checked_19456 n (by omega) (by omega)
          ·
            by_cases h19840 : n < 19840
            ·
              by_cases h19712 : n < 19712
              ·
                exact shapeBlock_spec 19584 128 shape_checked_19584 n (by omega) (by omega)
              ·
                exact shapeBlock_spec 19712 128 shape_checked_19712 n (by omega) (by omega)
            ·
              by_cases h19968 : n < 19968
              ·
                exact shapeBlock_spec 19840 128 shape_checked_19840 n (by omega) (by omega)
              ·
                by_cases h20096 : n < 20096
                ·
                  exact shapeBlock_spec 19968 128 shape_checked_19968 n (by omega) (by omega)
                ·
                  exact shapeBlock_spec 20096 64 shape_checked_20096 n (by omega) (by omega)

def encode (a : Letter (Fin 3)) : Nat := 2 * a.1.val + if a.2 then 0 else 1

theorem encode_lt (a : Letter (Fin 3)) : encode a < 6 := by
  have h := a.1.isLt
  unfold encode
  split <;> omega

theorem decode_encode (a : Letter (Fin 3)) : decode (encode a) = a := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide +kernel

theorem shape (i : Fin 3360) (a : Letter (Fin 3)) :
    facts (output (6 * i.val + encode a)) =
      ⟨index i, [a], index (dest (6 * i.val + encode a))⟩ := by
  have ha := encode_lt a
  have hi := i.isLt
  have hn : 6 * i.val + encode a < 20160 := by omega
  have hh := shape_all (6 * i.val + encode a) hn
  have hrow : (6 * i.val + encode a) / 6 % 3360 = i.val := by omega
  have hcol : (6 * i.val + encode a) % 6 = encode a := by omega
  have hfin : (⟨(6 * i.val + encode a) / 6 % 3360,
      Nat.mod_lt _ (by decide)⟩ : Fin 3360) = i := Fin.ext hrow
  simp only [shapeAt, hfin, hcol, decode_encode] at hh
  exact (factBEq_eq_true_iff _ _).mp hh

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.Bound.LocalFinite.Certificate
