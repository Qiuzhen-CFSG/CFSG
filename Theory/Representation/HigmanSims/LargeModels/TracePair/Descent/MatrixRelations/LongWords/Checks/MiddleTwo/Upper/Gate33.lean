module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Upper.Checker
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Tail

/-!
# Checked upper middle product gate 33

Every eight-row range is checked against the literal circuit operands by the
Lean kernel. The range assembly covers the first 880 rows; the final sixteen are reused from `Tail`.
Declaration checking is sequential to bound concurrent reduction caches;
Lean's process thread setting is unchanged. See `Upper/source/README.md`.
-/

set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper

private theorem block000 : CheckedRange 33 0 8 :=
  checkedRange_of_check 33 0 8 (by decide +kernel)

private theorem block008 : CheckedRange 33 8 8 :=
  checkedRange_of_check 33 8 8 (by decide +kernel)

private theorem block016 : CheckedRange 33 16 8 :=
  checkedRange_of_check 33 16 8 (by decide +kernel)

private theorem block024 : CheckedRange 33 24 8 :=
  checkedRange_of_check 33 24 8 (by decide +kernel)

private theorem block032 : CheckedRange 33 32 8 :=
  checkedRange_of_check 33 32 8 (by decide +kernel)

private theorem block040 : CheckedRange 33 40 8 :=
  checkedRange_of_check 33 40 8 (by decide +kernel)

private theorem block048 : CheckedRange 33 48 8 :=
  checkedRange_of_check 33 48 8 (by decide +kernel)

private theorem block056 : CheckedRange 33 56 8 :=
  checkedRange_of_check 33 56 8 (by decide +kernel)

private theorem block064 : CheckedRange 33 64 8 :=
  checkedRange_of_check 33 64 8 (by decide +kernel)

private theorem block072 : CheckedRange 33 72 8 :=
  checkedRange_of_check 33 72 8 (by decide +kernel)

private theorem block080 : CheckedRange 33 80 8 :=
  checkedRange_of_check 33 80 8 (by decide +kernel)

private theorem block088 : CheckedRange 33 88 8 :=
  checkedRange_of_check 33 88 8 (by decide +kernel)

private theorem block096 : CheckedRange 33 96 8 :=
  checkedRange_of_check 33 96 8 (by decide +kernel)

private theorem block104 : CheckedRange 33 104 8 :=
  checkedRange_of_check 33 104 8 (by decide +kernel)

private theorem block112 : CheckedRange 33 112 8 :=
  checkedRange_of_check 33 112 8 (by decide +kernel)

private theorem block120 : CheckedRange 33 120 8 :=
  checkedRange_of_check 33 120 8 (by decide +kernel)

private theorem block128 : CheckedRange 33 128 8 :=
  checkedRange_of_check 33 128 8 (by decide +kernel)

private theorem block136 : CheckedRange 33 136 8 :=
  checkedRange_of_check 33 136 8 (by decide +kernel)

private theorem block144 : CheckedRange 33 144 8 :=
  checkedRange_of_check 33 144 8 (by decide +kernel)

private theorem block152 : CheckedRange 33 152 8 :=
  checkedRange_of_check 33 152 8 (by decide +kernel)

private theorem block160 : CheckedRange 33 160 8 :=
  checkedRange_of_check 33 160 8 (by decide +kernel)

private theorem block168 : CheckedRange 33 168 8 :=
  checkedRange_of_check 33 168 8 (by decide +kernel)

private theorem block176 : CheckedRange 33 176 8 :=
  checkedRange_of_check 33 176 8 (by decide +kernel)

private theorem block184 : CheckedRange 33 184 8 :=
  checkedRange_of_check 33 184 8 (by decide +kernel)

private theorem block192 : CheckedRange 33 192 8 :=
  checkedRange_of_check 33 192 8 (by decide +kernel)

private theorem block200 : CheckedRange 33 200 8 :=
  checkedRange_of_check 33 200 8 (by decide +kernel)

private theorem block208 : CheckedRange 33 208 8 :=
  checkedRange_of_check 33 208 8 (by decide +kernel)

private theorem block216 : CheckedRange 33 216 8 :=
  checkedRange_of_check 33 216 8 (by decide +kernel)

private theorem block224 : CheckedRange 33 224 8 :=
  checkedRange_of_check 33 224 8 (by decide +kernel)

private theorem block232 : CheckedRange 33 232 8 :=
  checkedRange_of_check 33 232 8 (by decide +kernel)

private theorem block240 : CheckedRange 33 240 8 :=
  checkedRange_of_check 33 240 8 (by decide +kernel)

private theorem block248 : CheckedRange 33 248 8 :=
  checkedRange_of_check 33 248 8 (by decide +kernel)

private theorem block256 : CheckedRange 33 256 8 :=
  checkedRange_of_check 33 256 8 (by decide +kernel)

private theorem block264 : CheckedRange 33 264 8 :=
  checkedRange_of_check 33 264 8 (by decide +kernel)

private theorem block272 : CheckedRange 33 272 8 :=
  checkedRange_of_check 33 272 8 (by decide +kernel)

private theorem block280 : CheckedRange 33 280 8 :=
  checkedRange_of_check 33 280 8 (by decide +kernel)

private theorem block288 : CheckedRange 33 288 8 :=
  checkedRange_of_check 33 288 8 (by decide +kernel)

private theorem block296 : CheckedRange 33 296 8 :=
  checkedRange_of_check 33 296 8 (by decide +kernel)

private theorem block304 : CheckedRange 33 304 8 :=
  checkedRange_of_check 33 304 8 (by decide +kernel)

private theorem block312 : CheckedRange 33 312 8 :=
  checkedRange_of_check 33 312 8 (by decide +kernel)

private theorem block320 : CheckedRange 33 320 8 :=
  checkedRange_of_check 33 320 8 (by decide +kernel)

private theorem block328 : CheckedRange 33 328 8 :=
  checkedRange_of_check 33 328 8 (by decide +kernel)

private theorem block336 : CheckedRange 33 336 8 :=
  checkedRange_of_check 33 336 8 (by decide +kernel)

private theorem block344 : CheckedRange 33 344 8 :=
  checkedRange_of_check 33 344 8 (by decide +kernel)

private theorem block352 : CheckedRange 33 352 8 :=
  checkedRange_of_check 33 352 8 (by decide +kernel)

private theorem block360 : CheckedRange 33 360 8 :=
  checkedRange_of_check 33 360 8 (by decide +kernel)

private theorem block368 : CheckedRange 33 368 8 :=
  checkedRange_of_check 33 368 8 (by decide +kernel)

private theorem block376 : CheckedRange 33 376 8 :=
  checkedRange_of_check 33 376 8 (by decide +kernel)

private theorem block384 : CheckedRange 33 384 8 :=
  checkedRange_of_check 33 384 8 (by decide +kernel)

private theorem block392 : CheckedRange 33 392 8 :=
  checkedRange_of_check 33 392 8 (by decide +kernel)

private theorem block400 : CheckedRange 33 400 8 :=
  checkedRange_of_check 33 400 8 (by decide +kernel)

private theorem block408 : CheckedRange 33 408 8 :=
  checkedRange_of_check 33 408 8 (by decide +kernel)

private theorem block416 : CheckedRange 33 416 8 :=
  checkedRange_of_check 33 416 8 (by decide +kernel)

private theorem block424 : CheckedRange 33 424 8 :=
  checkedRange_of_check 33 424 8 (by decide +kernel)

private theorem block432 : CheckedRange 33 432 8 :=
  checkedRange_of_check 33 432 8 (by decide +kernel)

private theorem block440 : CheckedRange 33 440 8 :=
  checkedRange_of_check 33 440 8 (by decide +kernel)

private theorem block448 : CheckedRange 33 448 8 :=
  checkedRange_of_check 33 448 8 (by decide +kernel)

private theorem block456 : CheckedRange 33 456 8 :=
  checkedRange_of_check 33 456 8 (by decide +kernel)

private theorem block464 : CheckedRange 33 464 8 :=
  checkedRange_of_check 33 464 8 (by decide +kernel)

private theorem block472 : CheckedRange 33 472 8 :=
  checkedRange_of_check 33 472 8 (by decide +kernel)

private theorem block480 : CheckedRange 33 480 8 :=
  checkedRange_of_check 33 480 8 (by decide +kernel)

private theorem block488 : CheckedRange 33 488 8 :=
  checkedRange_of_check 33 488 8 (by decide +kernel)

private theorem block496 : CheckedRange 33 496 8 :=
  checkedRange_of_check 33 496 8 (by decide +kernel)

private theorem block504 : CheckedRange 33 504 8 :=
  checkedRange_of_check 33 504 8 (by decide +kernel)

private theorem block512 : CheckedRange 33 512 8 :=
  checkedRange_of_check 33 512 8 (by decide +kernel)

private theorem block520 : CheckedRange 33 520 8 :=
  checkedRange_of_check 33 520 8 (by decide +kernel)

private theorem block528 : CheckedRange 33 528 8 :=
  checkedRange_of_check 33 528 8 (by decide +kernel)

private theorem block536 : CheckedRange 33 536 8 :=
  checkedRange_of_check 33 536 8 (by decide +kernel)

private theorem block544 : CheckedRange 33 544 8 :=
  checkedRange_of_check 33 544 8 (by decide +kernel)

private theorem block552 : CheckedRange 33 552 8 :=
  checkedRange_of_check 33 552 8 (by decide +kernel)

private theorem block560 : CheckedRange 33 560 8 :=
  checkedRange_of_check 33 560 8 (by decide +kernel)

private theorem block568 : CheckedRange 33 568 8 :=
  checkedRange_of_check 33 568 8 (by decide +kernel)

private theorem block576 : CheckedRange 33 576 8 :=
  checkedRange_of_check 33 576 8 (by decide +kernel)

private theorem block584 : CheckedRange 33 584 8 :=
  checkedRange_of_check 33 584 8 (by decide +kernel)

private theorem block592 : CheckedRange 33 592 8 :=
  checkedRange_of_check 33 592 8 (by decide +kernel)

private theorem block600 : CheckedRange 33 600 8 :=
  checkedRange_of_check 33 600 8 (by decide +kernel)

private theorem block608 : CheckedRange 33 608 8 :=
  checkedRange_of_check 33 608 8 (by decide +kernel)

private theorem block616 : CheckedRange 33 616 8 :=
  checkedRange_of_check 33 616 8 (by decide +kernel)

private theorem block624 : CheckedRange 33 624 8 :=
  checkedRange_of_check 33 624 8 (by decide +kernel)

private theorem block632 : CheckedRange 33 632 8 :=
  checkedRange_of_check 33 632 8 (by decide +kernel)

private theorem block640 : CheckedRange 33 640 8 :=
  checkedRange_of_check 33 640 8 (by decide +kernel)

private theorem block648 : CheckedRange 33 648 8 :=
  checkedRange_of_check 33 648 8 (by decide +kernel)

private theorem block656 : CheckedRange 33 656 8 :=
  checkedRange_of_check 33 656 8 (by decide +kernel)

private theorem block664 : CheckedRange 33 664 8 :=
  checkedRange_of_check 33 664 8 (by decide +kernel)

private theorem block672 : CheckedRange 33 672 8 :=
  checkedRange_of_check 33 672 8 (by decide +kernel)

private theorem block680 : CheckedRange 33 680 8 :=
  checkedRange_of_check 33 680 8 (by decide +kernel)

private theorem block688 : CheckedRange 33 688 8 :=
  checkedRange_of_check 33 688 8 (by decide +kernel)

private theorem block696 : CheckedRange 33 696 8 :=
  checkedRange_of_check 33 696 8 (by decide +kernel)

private theorem block704 : CheckedRange 33 704 8 :=
  checkedRange_of_check 33 704 8 (by decide +kernel)

private theorem block712 : CheckedRange 33 712 8 :=
  checkedRange_of_check 33 712 8 (by decide +kernel)

private theorem block720 : CheckedRange 33 720 8 :=
  checkedRange_of_check 33 720 8 (by decide +kernel)

private theorem block728 : CheckedRange 33 728 8 :=
  checkedRange_of_check 33 728 8 (by decide +kernel)

private theorem block736 : CheckedRange 33 736 8 :=
  checkedRange_of_check 33 736 8 (by decide +kernel)

private theorem block744 : CheckedRange 33 744 8 :=
  checkedRange_of_check 33 744 8 (by decide +kernel)

private theorem block752 : CheckedRange 33 752 8 :=
  checkedRange_of_check 33 752 8 (by decide +kernel)

private theorem block760 : CheckedRange 33 760 8 :=
  checkedRange_of_check 33 760 8 (by decide +kernel)

private theorem block768 : CheckedRange 33 768 8 :=
  checkedRange_of_check 33 768 8 (by decide +kernel)

private theorem block776 : CheckedRange 33 776 8 :=
  checkedRange_of_check 33 776 8 (by decide +kernel)

private theorem block784 : CheckedRange 33 784 8 :=
  checkedRange_of_check 33 784 8 (by decide +kernel)

private theorem block792 : CheckedRange 33 792 8 :=
  checkedRange_of_check 33 792 8 (by decide +kernel)

private theorem block800 : CheckedRange 33 800 8 :=
  checkedRange_of_check 33 800 8 (by decide +kernel)

private theorem block808 : CheckedRange 33 808 8 :=
  checkedRange_of_check 33 808 8 (by decide +kernel)

private theorem block816 : CheckedRange 33 816 8 :=
  checkedRange_of_check 33 816 8 (by decide +kernel)

private theorem block824 : CheckedRange 33 824 8 :=
  checkedRange_of_check 33 824 8 (by decide +kernel)

private theorem block832 : CheckedRange 33 832 8 :=
  checkedRange_of_check 33 832 8 (by decide +kernel)

private theorem block840 : CheckedRange 33 840 8 :=
  checkedRange_of_check 33 840 8 (by decide +kernel)

private theorem block848 : CheckedRange 33 848 8 :=
  checkedRange_of_check 33 848 8 (by decide +kernel)

private theorem block856 : CheckedRange 33 856 8 :=
  checkedRange_of_check 33 856 8 (by decide +kernel)

private theorem block864 : CheckedRange 33 864 8 :=
  checkedRange_of_check 33 864 8 (by decide +kernel)

private theorem block872 : CheckedRange 33 872 8 :=
  checkedRange_of_check 33 872 8 (by decide +kernel)

private theorem all_rows : CheckedRange 33 0 880 :=
  (checkedRange_append 33 0 440 440
    (checkedRange_append 33 0 216 224
      (checkedRange_append 33 0 104 112
        (checkedRange_append 33 0 48 56
          (checkedRange_append 33 0 24 24
            (checkedRange_append 33 0 8 16
              block000
              (checkedRange_append 33 8 8 8
                block008
                block016))
            (checkedRange_append 33 24 8 16
              block024
              (checkedRange_append 33 32 8 8
                block032
                block040)))
          (checkedRange_append 33 48 24 32
            (checkedRange_append 33 48 8 16
              block048
              (checkedRange_append 33 56 8 8
                block056
                block064))
            (checkedRange_append 33 72 16 16
              (checkedRange_append 33 72 8 8
                block072
                block080)
              (checkedRange_append 33 88 8 8
                block088
                block096))))
        (checkedRange_append 33 104 56 56
          (checkedRange_append 33 104 24 32
            (checkedRange_append 33 104 8 16
              block104
              (checkedRange_append 33 112 8 8
                block112
                block120))
            (checkedRange_append 33 128 16 16
              (checkedRange_append 33 128 8 8
                block128
                block136)
              (checkedRange_append 33 144 8 8
                block144
                block152)))
          (checkedRange_append 33 160 24 32
            (checkedRange_append 33 160 8 16
              block160
              (checkedRange_append 33 168 8 8
                block168
                block176))
            (checkedRange_append 33 184 16 16
              (checkedRange_append 33 184 8 8
                block184
                block192)
              (checkedRange_append 33 200 8 8
                block200
                block208)))))
      (checkedRange_append 33 216 112 112
        (checkedRange_append 33 216 56 56
          (checkedRange_append 33 216 24 32
            (checkedRange_append 33 216 8 16
              block216
              (checkedRange_append 33 224 8 8
                block224
                block232))
            (checkedRange_append 33 240 16 16
              (checkedRange_append 33 240 8 8
                block240
                block248)
              (checkedRange_append 33 256 8 8
                block256
                block264)))
          (checkedRange_append 33 272 24 32
            (checkedRange_append 33 272 8 16
              block272
              (checkedRange_append 33 280 8 8
                block280
                block288))
            (checkedRange_append 33 296 16 16
              (checkedRange_append 33 296 8 8
                block296
                block304)
              (checkedRange_append 33 312 8 8
                block312
                block320))))
        (checkedRange_append 33 328 56 56
          (checkedRange_append 33 328 24 32
            (checkedRange_append 33 328 8 16
              block328
              (checkedRange_append 33 336 8 8
                block336
                block344))
            (checkedRange_append 33 352 16 16
              (checkedRange_append 33 352 8 8
                block352
                block360)
              (checkedRange_append 33 368 8 8
                block368
                block376)))
          (checkedRange_append 33 384 24 32
            (checkedRange_append 33 384 8 16
              block384
              (checkedRange_append 33 392 8 8
                block392
                block400))
            (checkedRange_append 33 408 16 16
              (checkedRange_append 33 408 8 8
                block408
                block416)
              (checkedRange_append 33 424 8 8
                block424
                block432))))))
    (checkedRange_append 33 440 216 224
      (checkedRange_append 33 440 104 112
        (checkedRange_append 33 440 48 56
          (checkedRange_append 33 440 24 24
            (checkedRange_append 33 440 8 16
              block440
              (checkedRange_append 33 448 8 8
                block448
                block456))
            (checkedRange_append 33 464 8 16
              block464
              (checkedRange_append 33 472 8 8
                block472
                block480)))
          (checkedRange_append 33 488 24 32
            (checkedRange_append 33 488 8 16
              block488
              (checkedRange_append 33 496 8 8
                block496
                block504))
            (checkedRange_append 33 512 16 16
              (checkedRange_append 33 512 8 8
                block512
                block520)
              (checkedRange_append 33 528 8 8
                block528
                block536))))
        (checkedRange_append 33 544 56 56
          (checkedRange_append 33 544 24 32
            (checkedRange_append 33 544 8 16
              block544
              (checkedRange_append 33 552 8 8
                block552
                block560))
            (checkedRange_append 33 568 16 16
              (checkedRange_append 33 568 8 8
                block568
                block576)
              (checkedRange_append 33 584 8 8
                block584
                block592)))
          (checkedRange_append 33 600 24 32
            (checkedRange_append 33 600 8 16
              block600
              (checkedRange_append 33 608 8 8
                block608
                block616))
            (checkedRange_append 33 624 16 16
              (checkedRange_append 33 624 8 8
                block624
                block632)
              (checkedRange_append 33 640 8 8
                block640
                block648)))))
      (checkedRange_append 33 656 112 112
        (checkedRange_append 33 656 56 56
          (checkedRange_append 33 656 24 32
            (checkedRange_append 33 656 8 16
              block656
              (checkedRange_append 33 664 8 8
                block664
                block672))
            (checkedRange_append 33 680 16 16
              (checkedRange_append 33 680 8 8
                block680
                block688)
              (checkedRange_append 33 696 8 8
                block696
                block704)))
          (checkedRange_append 33 712 24 32
            (checkedRange_append 33 712 8 16
              block712
              (checkedRange_append 33 720 8 8
                block720
                block728))
            (checkedRange_append 33 736 16 16
              (checkedRange_append 33 736 8 8
                block736
                block744)
              (checkedRange_append 33 752 8 8
                block752
                block760))))
        (checkedRange_append 33 768 56 56
          (checkedRange_append 33 768 24 32
            (checkedRange_append 33 768 8 16
              block768
              (checkedRange_append 33 776 8 8
                block776
                block784))
            (checkedRange_append 33 792 16 16
              (checkedRange_append 33 792 8 8
                block792
                block800)
              (checkedRange_append 33 808 8 8
                block808
                block816)))
          (checkedRange_append 33 824 24 32
            (checkedRange_append 33 824 8 16
              block824
              (checkedRange_append 33 832 8 8
                block832
                block840))
            (checkedRange_append 33 848 16 16
              (checkedRange_append 33 848 8 8
                block848
                block856)
              (checkedRange_append 33 864 8 8
                block864
                block872)))))))

/-- The complete fixed numerical product at gate 33. -/
theorem gate33_checked : ProductCheck 33 := by
  apply product_33_of_head
  intro r hr
  exact row_eq_of_check 33 r.val (all_rows r.val (Nat.zero_le _) hr)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Upper
