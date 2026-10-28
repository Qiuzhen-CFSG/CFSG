module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Checker

/-!
# Checked upper middle product gate 32

Every eight-row range is checked against the literal circuit operands by the
Lean kernel. The range assembly covers all 896 rows.
Declaration checking is sequential to bound concurrent reduction caches;
Lean's process thread setting is unchanged. See `Upper/source/README.md`.
-/

set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper

private theorem block000 : CheckedRange 32 0 8 :=
  checkedRange_of_check 32 0 8 (by decide +kernel)

private theorem block008 : CheckedRange 32 8 8 :=
  checkedRange_of_check 32 8 8 (by decide +kernel)

private theorem block016 : CheckedRange 32 16 8 :=
  checkedRange_of_check 32 16 8 (by decide +kernel)

private theorem block024 : CheckedRange 32 24 8 :=
  checkedRange_of_check 32 24 8 (by decide +kernel)

private theorem block032 : CheckedRange 32 32 8 :=
  checkedRange_of_check 32 32 8 (by decide +kernel)

private theorem block040 : CheckedRange 32 40 8 :=
  checkedRange_of_check 32 40 8 (by decide +kernel)

private theorem block048 : CheckedRange 32 48 8 :=
  checkedRange_of_check 32 48 8 (by decide +kernel)

private theorem block056 : CheckedRange 32 56 8 :=
  checkedRange_of_check 32 56 8 (by decide +kernel)

private theorem block064 : CheckedRange 32 64 8 :=
  checkedRange_of_check 32 64 8 (by decide +kernel)

private theorem block072 : CheckedRange 32 72 8 :=
  checkedRange_of_check 32 72 8 (by decide +kernel)

private theorem block080 : CheckedRange 32 80 8 :=
  checkedRange_of_check 32 80 8 (by decide +kernel)

private theorem block088 : CheckedRange 32 88 8 :=
  checkedRange_of_check 32 88 8 (by decide +kernel)

private theorem block096 : CheckedRange 32 96 8 :=
  checkedRange_of_check 32 96 8 (by decide +kernel)

private theorem block104 : CheckedRange 32 104 8 :=
  checkedRange_of_check 32 104 8 (by decide +kernel)

private theorem block112 : CheckedRange 32 112 8 :=
  checkedRange_of_check 32 112 8 (by decide +kernel)

private theorem block120 : CheckedRange 32 120 8 :=
  checkedRange_of_check 32 120 8 (by decide +kernel)

private theorem block128 : CheckedRange 32 128 8 :=
  checkedRange_of_check 32 128 8 (by decide +kernel)

private theorem block136 : CheckedRange 32 136 8 :=
  checkedRange_of_check 32 136 8 (by decide +kernel)

private theorem block144 : CheckedRange 32 144 8 :=
  checkedRange_of_check 32 144 8 (by decide +kernel)

private theorem block152 : CheckedRange 32 152 8 :=
  checkedRange_of_check 32 152 8 (by decide +kernel)

private theorem block160 : CheckedRange 32 160 8 :=
  checkedRange_of_check 32 160 8 (by decide +kernel)

private theorem block168 : CheckedRange 32 168 8 :=
  checkedRange_of_check 32 168 8 (by decide +kernel)

private theorem block176 : CheckedRange 32 176 8 :=
  checkedRange_of_check 32 176 8 (by decide +kernel)

private theorem block184 : CheckedRange 32 184 8 :=
  checkedRange_of_check 32 184 8 (by decide +kernel)

private theorem block192 : CheckedRange 32 192 8 :=
  checkedRange_of_check 32 192 8 (by decide +kernel)

private theorem block200 : CheckedRange 32 200 8 :=
  checkedRange_of_check 32 200 8 (by decide +kernel)

private theorem block208 : CheckedRange 32 208 8 :=
  checkedRange_of_check 32 208 8 (by decide +kernel)

private theorem block216 : CheckedRange 32 216 8 :=
  checkedRange_of_check 32 216 8 (by decide +kernel)

private theorem block224 : CheckedRange 32 224 8 :=
  checkedRange_of_check 32 224 8 (by decide +kernel)

private theorem block232 : CheckedRange 32 232 8 :=
  checkedRange_of_check 32 232 8 (by decide +kernel)

private theorem block240 : CheckedRange 32 240 8 :=
  checkedRange_of_check 32 240 8 (by decide +kernel)

private theorem block248 : CheckedRange 32 248 8 :=
  checkedRange_of_check 32 248 8 (by decide +kernel)

private theorem block256 : CheckedRange 32 256 8 :=
  checkedRange_of_check 32 256 8 (by decide +kernel)

private theorem block264 : CheckedRange 32 264 8 :=
  checkedRange_of_check 32 264 8 (by decide +kernel)

private theorem block272 : CheckedRange 32 272 8 :=
  checkedRange_of_check 32 272 8 (by decide +kernel)

private theorem block280 : CheckedRange 32 280 8 :=
  checkedRange_of_check 32 280 8 (by decide +kernel)

private theorem block288 : CheckedRange 32 288 8 :=
  checkedRange_of_check 32 288 8 (by decide +kernel)

private theorem block296 : CheckedRange 32 296 8 :=
  checkedRange_of_check 32 296 8 (by decide +kernel)

private theorem block304 : CheckedRange 32 304 8 :=
  checkedRange_of_check 32 304 8 (by decide +kernel)

private theorem block312 : CheckedRange 32 312 8 :=
  checkedRange_of_check 32 312 8 (by decide +kernel)

private theorem block320 : CheckedRange 32 320 8 :=
  checkedRange_of_check 32 320 8 (by decide +kernel)

private theorem block328 : CheckedRange 32 328 8 :=
  checkedRange_of_check 32 328 8 (by decide +kernel)

private theorem block336 : CheckedRange 32 336 8 :=
  checkedRange_of_check 32 336 8 (by decide +kernel)

private theorem block344 : CheckedRange 32 344 8 :=
  checkedRange_of_check 32 344 8 (by decide +kernel)

private theorem block352 : CheckedRange 32 352 8 :=
  checkedRange_of_check 32 352 8 (by decide +kernel)

private theorem block360 : CheckedRange 32 360 8 :=
  checkedRange_of_check 32 360 8 (by decide +kernel)

private theorem block368 : CheckedRange 32 368 8 :=
  checkedRange_of_check 32 368 8 (by decide +kernel)

private theorem block376 : CheckedRange 32 376 8 :=
  checkedRange_of_check 32 376 8 (by decide +kernel)

private theorem block384 : CheckedRange 32 384 8 :=
  checkedRange_of_check 32 384 8 (by decide +kernel)

private theorem block392 : CheckedRange 32 392 8 :=
  checkedRange_of_check 32 392 8 (by decide +kernel)

private theorem block400 : CheckedRange 32 400 8 :=
  checkedRange_of_check 32 400 8 (by decide +kernel)

private theorem block408 : CheckedRange 32 408 8 :=
  checkedRange_of_check 32 408 8 (by decide +kernel)

private theorem block416 : CheckedRange 32 416 8 :=
  checkedRange_of_check 32 416 8 (by decide +kernel)

private theorem block424 : CheckedRange 32 424 8 :=
  checkedRange_of_check 32 424 8 (by decide +kernel)

private theorem block432 : CheckedRange 32 432 8 :=
  checkedRange_of_check 32 432 8 (by decide +kernel)

private theorem block440 : CheckedRange 32 440 8 :=
  checkedRange_of_check 32 440 8 (by decide +kernel)

private theorem block448 : CheckedRange 32 448 8 :=
  checkedRange_of_check 32 448 8 (by decide +kernel)

private theorem block456 : CheckedRange 32 456 8 :=
  checkedRange_of_check 32 456 8 (by decide +kernel)

private theorem block464 : CheckedRange 32 464 8 :=
  checkedRange_of_check 32 464 8 (by decide +kernel)

private theorem block472 : CheckedRange 32 472 8 :=
  checkedRange_of_check 32 472 8 (by decide +kernel)

private theorem block480 : CheckedRange 32 480 8 :=
  checkedRange_of_check 32 480 8 (by decide +kernel)

private theorem block488 : CheckedRange 32 488 8 :=
  checkedRange_of_check 32 488 8 (by decide +kernel)

private theorem block496 : CheckedRange 32 496 8 :=
  checkedRange_of_check 32 496 8 (by decide +kernel)

private theorem block504 : CheckedRange 32 504 8 :=
  checkedRange_of_check 32 504 8 (by decide +kernel)

private theorem block512 : CheckedRange 32 512 8 :=
  checkedRange_of_check 32 512 8 (by decide +kernel)

private theorem block520 : CheckedRange 32 520 8 :=
  checkedRange_of_check 32 520 8 (by decide +kernel)

private theorem block528 : CheckedRange 32 528 8 :=
  checkedRange_of_check 32 528 8 (by decide +kernel)

private theorem block536 : CheckedRange 32 536 8 :=
  checkedRange_of_check 32 536 8 (by decide +kernel)

private theorem block544 : CheckedRange 32 544 8 :=
  checkedRange_of_check 32 544 8 (by decide +kernel)

private theorem block552 : CheckedRange 32 552 8 :=
  checkedRange_of_check 32 552 8 (by decide +kernel)

private theorem block560 : CheckedRange 32 560 8 :=
  checkedRange_of_check 32 560 8 (by decide +kernel)

private theorem block568 : CheckedRange 32 568 8 :=
  checkedRange_of_check 32 568 8 (by decide +kernel)

private theorem block576 : CheckedRange 32 576 8 :=
  checkedRange_of_check 32 576 8 (by decide +kernel)

private theorem block584 : CheckedRange 32 584 8 :=
  checkedRange_of_check 32 584 8 (by decide +kernel)

private theorem block592 : CheckedRange 32 592 8 :=
  checkedRange_of_check 32 592 8 (by decide +kernel)

private theorem block600 : CheckedRange 32 600 8 :=
  checkedRange_of_check 32 600 8 (by decide +kernel)

private theorem block608 : CheckedRange 32 608 8 :=
  checkedRange_of_check 32 608 8 (by decide +kernel)

private theorem block616 : CheckedRange 32 616 8 :=
  checkedRange_of_check 32 616 8 (by decide +kernel)

private theorem block624 : CheckedRange 32 624 8 :=
  checkedRange_of_check 32 624 8 (by decide +kernel)

private theorem block632 : CheckedRange 32 632 8 :=
  checkedRange_of_check 32 632 8 (by decide +kernel)

private theorem block640 : CheckedRange 32 640 8 :=
  checkedRange_of_check 32 640 8 (by decide +kernel)

private theorem block648 : CheckedRange 32 648 8 :=
  checkedRange_of_check 32 648 8 (by decide +kernel)

private theorem block656 : CheckedRange 32 656 8 :=
  checkedRange_of_check 32 656 8 (by decide +kernel)

private theorem block664 : CheckedRange 32 664 8 :=
  checkedRange_of_check 32 664 8 (by decide +kernel)

private theorem block672 : CheckedRange 32 672 8 :=
  checkedRange_of_check 32 672 8 (by decide +kernel)

private theorem block680 : CheckedRange 32 680 8 :=
  checkedRange_of_check 32 680 8 (by decide +kernel)

private theorem block688 : CheckedRange 32 688 8 :=
  checkedRange_of_check 32 688 8 (by decide +kernel)

private theorem block696 : CheckedRange 32 696 8 :=
  checkedRange_of_check 32 696 8 (by decide +kernel)

private theorem block704 : CheckedRange 32 704 8 :=
  checkedRange_of_check 32 704 8 (by decide +kernel)

private theorem block712 : CheckedRange 32 712 8 :=
  checkedRange_of_check 32 712 8 (by decide +kernel)

private theorem block720 : CheckedRange 32 720 8 :=
  checkedRange_of_check 32 720 8 (by decide +kernel)

private theorem block728 : CheckedRange 32 728 8 :=
  checkedRange_of_check 32 728 8 (by decide +kernel)

private theorem block736 : CheckedRange 32 736 8 :=
  checkedRange_of_check 32 736 8 (by decide +kernel)

private theorem block744 : CheckedRange 32 744 8 :=
  checkedRange_of_check 32 744 8 (by decide +kernel)

private theorem block752 : CheckedRange 32 752 8 :=
  checkedRange_of_check 32 752 8 (by decide +kernel)

private theorem block760 : CheckedRange 32 760 8 :=
  checkedRange_of_check 32 760 8 (by decide +kernel)

private theorem block768 : CheckedRange 32 768 8 :=
  checkedRange_of_check 32 768 8 (by decide +kernel)

private theorem block776 : CheckedRange 32 776 8 :=
  checkedRange_of_check 32 776 8 (by decide +kernel)

private theorem block784 : CheckedRange 32 784 8 :=
  checkedRange_of_check 32 784 8 (by decide +kernel)

private theorem block792 : CheckedRange 32 792 8 :=
  checkedRange_of_check 32 792 8 (by decide +kernel)

private theorem block800 : CheckedRange 32 800 8 :=
  checkedRange_of_check 32 800 8 (by decide +kernel)

private theorem block808 : CheckedRange 32 808 8 :=
  checkedRange_of_check 32 808 8 (by decide +kernel)

private theorem block816 : CheckedRange 32 816 8 :=
  checkedRange_of_check 32 816 8 (by decide +kernel)

private theorem block824 : CheckedRange 32 824 8 :=
  checkedRange_of_check 32 824 8 (by decide +kernel)

private theorem block832 : CheckedRange 32 832 8 :=
  checkedRange_of_check 32 832 8 (by decide +kernel)

private theorem block840 : CheckedRange 32 840 8 :=
  checkedRange_of_check 32 840 8 (by decide +kernel)

private theorem block848 : CheckedRange 32 848 8 :=
  checkedRange_of_check 32 848 8 (by decide +kernel)

private theorem block856 : CheckedRange 32 856 8 :=
  checkedRange_of_check 32 856 8 (by decide +kernel)

private theorem block864 : CheckedRange 32 864 8 :=
  checkedRange_of_check 32 864 8 (by decide +kernel)

private theorem block872 : CheckedRange 32 872 8 :=
  checkedRange_of_check 32 872 8 (by decide +kernel)

private theorem block880 : CheckedRange 32 880 8 :=
  checkedRange_of_check 32 880 8 (by decide +kernel)

private theorem block888 : CheckedRange 32 888 8 :=
  checkedRange_of_check 32 888 8 (by decide +kernel)

private theorem all_rows : CheckedRange 32 0 896 :=
  (checkedRange_append 32 0 448 448
    (checkedRange_append 32 0 224 224
      (checkedRange_append 32 0 112 112
        (checkedRange_append 32 0 56 56
          (checkedRange_append 32 0 24 32
            (checkedRange_append 32 0 8 16
              block000
              (checkedRange_append 32 8 8 8
                block008
                block016))
            (checkedRange_append 32 24 16 16
              (checkedRange_append 32 24 8 8
                block024
                block032)
              (checkedRange_append 32 40 8 8
                block040
                block048)))
          (checkedRange_append 32 56 24 32
            (checkedRange_append 32 56 8 16
              block056
              (checkedRange_append 32 64 8 8
                block064
                block072))
            (checkedRange_append 32 80 16 16
              (checkedRange_append 32 80 8 8
                block080
                block088)
              (checkedRange_append 32 96 8 8
                block096
                block104))))
        (checkedRange_append 32 112 56 56
          (checkedRange_append 32 112 24 32
            (checkedRange_append 32 112 8 16
              block112
              (checkedRange_append 32 120 8 8
                block120
                block128))
            (checkedRange_append 32 136 16 16
              (checkedRange_append 32 136 8 8
                block136
                block144)
              (checkedRange_append 32 152 8 8
                block152
                block160)))
          (checkedRange_append 32 168 24 32
            (checkedRange_append 32 168 8 16
              block168
              (checkedRange_append 32 176 8 8
                block176
                block184))
            (checkedRange_append 32 192 16 16
              (checkedRange_append 32 192 8 8
                block192
                block200)
              (checkedRange_append 32 208 8 8
                block208
                block216)))))
      (checkedRange_append 32 224 112 112
        (checkedRange_append 32 224 56 56
          (checkedRange_append 32 224 24 32
            (checkedRange_append 32 224 8 16
              block224
              (checkedRange_append 32 232 8 8
                block232
                block240))
            (checkedRange_append 32 248 16 16
              (checkedRange_append 32 248 8 8
                block248
                block256)
              (checkedRange_append 32 264 8 8
                block264
                block272)))
          (checkedRange_append 32 280 24 32
            (checkedRange_append 32 280 8 16
              block280
              (checkedRange_append 32 288 8 8
                block288
                block296))
            (checkedRange_append 32 304 16 16
              (checkedRange_append 32 304 8 8
                block304
                block312)
              (checkedRange_append 32 320 8 8
                block320
                block328))))
        (checkedRange_append 32 336 56 56
          (checkedRange_append 32 336 24 32
            (checkedRange_append 32 336 8 16
              block336
              (checkedRange_append 32 344 8 8
                block344
                block352))
            (checkedRange_append 32 360 16 16
              (checkedRange_append 32 360 8 8
                block360
                block368)
              (checkedRange_append 32 376 8 8
                block376
                block384)))
          (checkedRange_append 32 392 24 32
            (checkedRange_append 32 392 8 16
              block392
              (checkedRange_append 32 400 8 8
                block400
                block408))
            (checkedRange_append 32 416 16 16
              (checkedRange_append 32 416 8 8
                block416
                block424)
              (checkedRange_append 32 432 8 8
                block432
                block440))))))
    (checkedRange_append 32 448 224 224
      (checkedRange_append 32 448 112 112
        (checkedRange_append 32 448 56 56
          (checkedRange_append 32 448 24 32
            (checkedRange_append 32 448 8 16
              block448
              (checkedRange_append 32 456 8 8
                block456
                block464))
            (checkedRange_append 32 472 16 16
              (checkedRange_append 32 472 8 8
                block472
                block480)
              (checkedRange_append 32 488 8 8
                block488
                block496)))
          (checkedRange_append 32 504 24 32
            (checkedRange_append 32 504 8 16
              block504
              (checkedRange_append 32 512 8 8
                block512
                block520))
            (checkedRange_append 32 528 16 16
              (checkedRange_append 32 528 8 8
                block528
                block536)
              (checkedRange_append 32 544 8 8
                block544
                block552))))
        (checkedRange_append 32 560 56 56
          (checkedRange_append 32 560 24 32
            (checkedRange_append 32 560 8 16
              block560
              (checkedRange_append 32 568 8 8
                block568
                block576))
            (checkedRange_append 32 584 16 16
              (checkedRange_append 32 584 8 8
                block584
                block592)
              (checkedRange_append 32 600 8 8
                block600
                block608)))
          (checkedRange_append 32 616 24 32
            (checkedRange_append 32 616 8 16
              block616
              (checkedRange_append 32 624 8 8
                block624
                block632))
            (checkedRange_append 32 640 16 16
              (checkedRange_append 32 640 8 8
                block640
                block648)
              (checkedRange_append 32 656 8 8
                block656
                block664)))))
      (checkedRange_append 32 672 112 112
        (checkedRange_append 32 672 56 56
          (checkedRange_append 32 672 24 32
            (checkedRange_append 32 672 8 16
              block672
              (checkedRange_append 32 680 8 8
                block680
                block688))
            (checkedRange_append 32 696 16 16
              (checkedRange_append 32 696 8 8
                block696
                block704)
              (checkedRange_append 32 712 8 8
                block712
                block720)))
          (checkedRange_append 32 728 24 32
            (checkedRange_append 32 728 8 16
              block728
              (checkedRange_append 32 736 8 8
                block736
                block744))
            (checkedRange_append 32 752 16 16
              (checkedRange_append 32 752 8 8
                block752
                block760)
              (checkedRange_append 32 768 8 8
                block768
                block776))))
        (checkedRange_append 32 784 56 56
          (checkedRange_append 32 784 24 32
            (checkedRange_append 32 784 8 16
              block784
              (checkedRange_append 32 792 8 8
                block792
                block800))
            (checkedRange_append 32 808 16 16
              (checkedRange_append 32 808 8 8
                block808
                block816)
              (checkedRange_append 32 824 8 8
                block824
                block832)))
          (checkedRange_append 32 840 24 32
            (checkedRange_append 32 840 8 16
              block840
              (checkedRange_append 32 848 8 8
                block848
                block856))
            (checkedRange_append 32 864 16 16
              (checkedRange_append 32 864 8 8
                block864
                block872)
              (checkedRange_append 32 880 8 8
                block880
                block888)))))))

/-- The complete fixed numerical product at gate 32. -/
theorem gate32_checked : ProductCheck 32 := productCheck_of_checked 32 all_rows

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper
