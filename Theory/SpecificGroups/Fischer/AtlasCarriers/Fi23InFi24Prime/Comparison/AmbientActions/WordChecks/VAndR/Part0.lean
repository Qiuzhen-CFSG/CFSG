module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 0

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block0 : checkPow pointTest 0 6 = true := by
  decide +kernel

private theorem block1 : checkPow pointTest 64 6 = true := by
  decide +kernel

private theorem block2 : checkPow pointTest 128 6 = true := by
  decide +kernel

private theorem block3 : checkPow pointTest 192 6 = true := by
  decide +kernel

private theorem block4 : checkPow pointTest 256 6 = true := by
  decide +kernel

private theorem block5 : checkPow pointTest 320 6 = true := by
  decide +kernel

private theorem block6 : checkPow pointTest 384 6 = true := by
  decide +kernel

private theorem block7 : checkPow pointTest 448 6 = true := by
  decide +kernel

private theorem block8 : checkPow pointTest 512 6 = true := by
  decide +kernel

private theorem block9 : checkPow pointTest 576 6 = true := by
  decide +kernel

private theorem block10 : checkPow pointTest 640 6 = true := by
  decide +kernel

private theorem block11 : checkPow pointTest 704 6 = true := by
  decide +kernel

private theorem block12 : checkPow pointTest 768 6 = true := by
  decide +kernel

private theorem block13 : checkPow pointTest 832 6 = true := by
  decide +kernel

private theorem block14 : checkPow pointTest 896 6 = true := by
  decide +kernel

private theorem block15 : checkPow pointTest 960 6 = true := by
  decide +kernel

private theorem block16 : checkPow pointTest 1024 6 = true := by
  decide +kernel

private theorem block17 : checkPow pointTest 1088 6 = true := by
  decide +kernel

private theorem block18 : checkPow pointTest 1152 6 = true := by
  decide +kernel

private theorem block19 : checkPow pointTest 1216 6 = true := by
  decide +kernel

private theorem block20 : checkPow pointTest 1280 6 = true := by
  decide +kernel

private theorem block21 : checkPow pointTest 1344 6 = true := by
  decide +kernel

private theorem block22 : checkPow pointTest 1408 6 = true := by
  decide +kernel

private theorem block23 : checkPow pointTest 1472 6 = true := by
  decide +kernel

private theorem block24 : checkPow pointTest 1536 6 = true := by
  decide +kernel

private theorem block25 : checkPow pointTest 1600 6 = true := by
  decide +kernel

private theorem block26 : checkPow pointTest 1664 6 = true := by
  decide +kernel

private theorem block27 : checkPow pointTest 1728 6 = true := by
  decide +kernel

private theorem block28 : checkPow pointTest 1792 6 = true := by
  decide +kernel

private theorem block29 : checkPow pointTest 1856 6 = true := by
  decide +kernel

private theorem block30 : checkPow pointTest 1920 6 = true := by
  decide +kernel

private theorem block31 : checkPow pointTest 1984 6 = true := by
  decide +kernel

private theorem block32 : checkPow pointTest 2048 6 = true := by
  decide +kernel

private theorem block33 : checkPow pointTest 2112 6 = true := by
  decide +kernel

private theorem block34 : checkPow pointTest 2176 6 = true := by
  decide +kernel

private theorem block35 : checkPow pointTest 2240 6 = true := by
  decide +kernel

private theorem block36 : checkPow pointTest 2304 6 = true := by
  decide +kernel

private theorem block37 : checkPow pointTest 2368 6 = true := by
  decide +kernel

private theorem block38 : checkPow pointTest 2432 6 = true := by
  decide +kernel

private theorem block39 : checkPow pointTest 2496 6 = true := by
  decide +kernel

private theorem block40 : checkPow pointTest 2560 6 = true := by
  decide +kernel

private theorem block41 : checkPow pointTest 2624 6 = true := by
  decide +kernel

private theorem block42 : checkPow pointTest 2688 6 = true := by
  decide +kernel

private theorem block43 : checkPow pointTest 2752 6 = true := by
  decide +kernel

private theorem block44 : checkPow pointTest 2816 6 = true := by
  decide +kernel

private theorem block45 : checkPow pointTest 2880 6 = true := by
  decide +kernel

private theorem block46 : checkPow pointTest 2944 6 = true := by
  decide +kernel

private theorem block47 : checkPow pointTest 3008 6 = true := by
  decide +kernel

private theorem block48 : checkPow pointTest 3072 6 = true := by
  decide +kernel

private theorem block49 : checkPow pointTest 3136 6 = true := by
  decide +kernel

private theorem block50 : checkPow pointTest 3200 6 = true := by
  decide +kernel

private theorem block51 : checkPow pointTest 3264 6 = true := by
  decide +kernel

private theorem block52 : checkPow pointTest 3328 6 = true := by
  decide +kernel

private theorem block53 : checkPow pointTest 3392 6 = true := by
  decide +kernel

private theorem block54 : checkPow pointTest 3456 6 = true := by
  decide +kernel

private theorem block55 : checkPow pointTest 3520 6 = true := by
  decide +kernel

private theorem block56 : checkPow pointTest 3584 6 = true := by
  decide +kernel

private theorem block57 : checkPow pointTest 3648 6 = true := by
  decide +kernel

private theorem block58 : checkPow pointTest 3712 6 = true := by
  decide +kernel

private theorem block59 : checkPow pointTest 3776 6 = true := by
  decide +kernel

private theorem block60 : checkPow pointTest 3840 6 = true := by
  decide +kernel

private theorem block61 : checkPow pointTest 3904 6 = true := by
  decide +kernel

private theorem block62 : checkPow pointTest 3968 6 = true := by
  decide +kernel

private theorem block63 : checkPow pointTest 4032 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked0 : checkPow pointTest 0 12 = true :=
  (checkPow_join pointTest 11 0
    (checkPow_join pointTest 10 0
    (checkPow_join pointTest 9 0
    (checkPow_join pointTest 8 0
    (checkPow_join pointTest 7 0
    (checkPow_join pointTest 6 0
    block0
    block1)
    (checkPow_join pointTest 6 128
    block2
    block3))
    (checkPow_join pointTest 7 256
    (checkPow_join pointTest 6 256
    block4
    block5)
    (checkPow_join pointTest 6 384
    block6
    block7)))
    (checkPow_join pointTest 8 512
    (checkPow_join pointTest 7 512
    (checkPow_join pointTest 6 512
    block8
    block9)
    (checkPow_join pointTest 6 640
    block10
    block11))
    (checkPow_join pointTest 7 768
    (checkPow_join pointTest 6 768
    block12
    block13)
    (checkPow_join pointTest 6 896
    block14
    block15))))
    (checkPow_join pointTest 9 1024
    (checkPow_join pointTest 8 1024
    (checkPow_join pointTest 7 1024
    (checkPow_join pointTest 6 1024
    block16
    block17)
    (checkPow_join pointTest 6 1152
    block18
    block19))
    (checkPow_join pointTest 7 1280
    (checkPow_join pointTest 6 1280
    block20
    block21)
    (checkPow_join pointTest 6 1408
    block22
    block23)))
    (checkPow_join pointTest 8 1536
    (checkPow_join pointTest 7 1536
    (checkPow_join pointTest 6 1536
    block24
    block25)
    (checkPow_join pointTest 6 1664
    block26
    block27))
    (checkPow_join pointTest 7 1792
    (checkPow_join pointTest 6 1792
    block28
    block29)
    (checkPow_join pointTest 6 1920
    block30
    block31)))))
    (checkPow_join pointTest 10 2048
    (checkPow_join pointTest 9 2048
    (checkPow_join pointTest 8 2048
    (checkPow_join pointTest 7 2048
    (checkPow_join pointTest 6 2048
    block32
    block33)
    (checkPow_join pointTest 6 2176
    block34
    block35))
    (checkPow_join pointTest 7 2304
    (checkPow_join pointTest 6 2304
    block36
    block37)
    (checkPow_join pointTest 6 2432
    block38
    block39)))
    (checkPow_join pointTest 8 2560
    (checkPow_join pointTest 7 2560
    (checkPow_join pointTest 6 2560
    block40
    block41)
    (checkPow_join pointTest 6 2688
    block42
    block43))
    (checkPow_join pointTest 7 2816
    (checkPow_join pointTest 6 2816
    block44
    block45)
    (checkPow_join pointTest 6 2944
    block46
    block47))))
    (checkPow_join pointTest 9 3072
    (checkPow_join pointTest 8 3072
    (checkPow_join pointTest 7 3072
    (checkPow_join pointTest 6 3072
    block48
    block49)
    (checkPow_join pointTest 6 3200
    block50
    block51))
    (checkPow_join pointTest 7 3328
    (checkPow_join pointTest 6 3328
    block52
    block53)
    (checkPow_join pointTest 6 3456
    block54
    block55)))
    (checkPow_join pointTest 8 3584
    (checkPow_join pointTest 7 3584
    (checkPow_join pointTest 6 3584
    block56
    block57)
    (checkPow_join pointTest 6 3712
    block58
    block59))
    (checkPow_join pointTest 7 3840
    (checkPow_join pointTest 6 3840
    block60
    block61)
    (checkPow_join pointTest 6 3968
    block62
    block63))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
