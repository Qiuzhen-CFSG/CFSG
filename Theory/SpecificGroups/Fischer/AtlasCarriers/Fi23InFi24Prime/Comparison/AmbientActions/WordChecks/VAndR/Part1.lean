module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 4096

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block64 : checkPow pointTest 4096 6 = true := by
  decide +kernel

private theorem block65 : checkPow pointTest 4160 6 = true := by
  decide +kernel

private theorem block66 : checkPow pointTest 4224 6 = true := by
  decide +kernel

private theorem block67 : checkPow pointTest 4288 6 = true := by
  decide +kernel

private theorem block68 : checkPow pointTest 4352 6 = true := by
  decide +kernel

private theorem block69 : checkPow pointTest 4416 6 = true := by
  decide +kernel

private theorem block70 : checkPow pointTest 4480 6 = true := by
  decide +kernel

private theorem block71 : checkPow pointTest 4544 6 = true := by
  decide +kernel

private theorem block72 : checkPow pointTest 4608 6 = true := by
  decide +kernel

private theorem block73 : checkPow pointTest 4672 6 = true := by
  decide +kernel

private theorem block74 : checkPow pointTest 4736 6 = true := by
  decide +kernel

private theorem block75 : checkPow pointTest 4800 6 = true := by
  decide +kernel

private theorem block76 : checkPow pointTest 4864 6 = true := by
  decide +kernel

private theorem block77 : checkPow pointTest 4928 6 = true := by
  decide +kernel

private theorem block78 : checkPow pointTest 4992 6 = true := by
  decide +kernel

private theorem block79 : checkPow pointTest 5056 6 = true := by
  decide +kernel

private theorem block80 : checkPow pointTest 5120 6 = true := by
  decide +kernel

private theorem block81 : checkPow pointTest 5184 6 = true := by
  decide +kernel

private theorem block82 : checkPow pointTest 5248 6 = true := by
  decide +kernel

private theorem block83 : checkPow pointTest 5312 6 = true := by
  decide +kernel

private theorem block84 : checkPow pointTest 5376 6 = true := by
  decide +kernel

private theorem block85 : checkPow pointTest 5440 6 = true := by
  decide +kernel

private theorem block86 : checkPow pointTest 5504 6 = true := by
  decide +kernel

private theorem block87 : checkPow pointTest 5568 6 = true := by
  decide +kernel

private theorem block88 : checkPow pointTest 5632 6 = true := by
  decide +kernel

private theorem block89 : checkPow pointTest 5696 6 = true := by
  decide +kernel

private theorem block90 : checkPow pointTest 5760 6 = true := by
  decide +kernel

private theorem block91 : checkPow pointTest 5824 6 = true := by
  decide +kernel

private theorem block92 : checkPow pointTest 5888 6 = true := by
  decide +kernel

private theorem block93 : checkPow pointTest 5952 6 = true := by
  decide +kernel

private theorem block94 : checkPow pointTest 6016 6 = true := by
  decide +kernel

private theorem block95 : checkPow pointTest 6080 6 = true := by
  decide +kernel

private theorem block96 : checkPow pointTest 6144 6 = true := by
  decide +kernel

private theorem block97 : checkPow pointTest 6208 6 = true := by
  decide +kernel

private theorem block98 : checkPow pointTest 6272 6 = true := by
  decide +kernel

private theorem block99 : checkPow pointTest 6336 6 = true := by
  decide +kernel

private theorem block100 : checkPow pointTest 6400 6 = true := by
  decide +kernel

private theorem block101 : checkPow pointTest 6464 6 = true := by
  decide +kernel

private theorem block102 : checkPow pointTest 6528 6 = true := by
  decide +kernel

private theorem block103 : checkPow pointTest 6592 6 = true := by
  decide +kernel

private theorem block104 : checkPow pointTest 6656 6 = true := by
  decide +kernel

private theorem block105 : checkPow pointTest 6720 6 = true := by
  decide +kernel

private theorem block106 : checkPow pointTest 6784 6 = true := by
  decide +kernel

private theorem block107 : checkPow pointTest 6848 6 = true := by
  decide +kernel

private theorem block108 : checkPow pointTest 6912 6 = true := by
  decide +kernel

private theorem block109 : checkPow pointTest 6976 6 = true := by
  decide +kernel

private theorem block110 : checkPow pointTest 7040 6 = true := by
  decide +kernel

private theorem block111 : checkPow pointTest 7104 6 = true := by
  decide +kernel

private theorem block112 : checkPow pointTest 7168 6 = true := by
  decide +kernel

private theorem block113 : checkPow pointTest 7232 6 = true := by
  decide +kernel

private theorem block114 : checkPow pointTest 7296 6 = true := by
  decide +kernel

private theorem block115 : checkPow pointTest 7360 6 = true := by
  decide +kernel

private theorem block116 : checkPow pointTest 7424 6 = true := by
  decide +kernel

private theorem block117 : checkPow pointTest 7488 6 = true := by
  decide +kernel

private theorem block118 : checkPow pointTest 7552 6 = true := by
  decide +kernel

private theorem block119 : checkPow pointTest 7616 6 = true := by
  decide +kernel

private theorem block120 : checkPow pointTest 7680 6 = true := by
  decide +kernel

private theorem block121 : checkPow pointTest 7744 6 = true := by
  decide +kernel

private theorem block122 : checkPow pointTest 7808 6 = true := by
  decide +kernel

private theorem block123 : checkPow pointTest 7872 6 = true := by
  decide +kernel

private theorem block124 : checkPow pointTest 7936 6 = true := by
  decide +kernel

private theorem block125 : checkPow pointTest 8000 6 = true := by
  decide +kernel

private theorem block126 : checkPow pointTest 8064 6 = true := by
  decide +kernel

private theorem block127 : checkPow pointTest 8128 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked1 : checkPow pointTest 4096 12 = true :=
  (checkPow_join pointTest 11 4096
    (checkPow_join pointTest 10 4096
    (checkPow_join pointTest 9 4096
    (checkPow_join pointTest 8 4096
    (checkPow_join pointTest 7 4096
    (checkPow_join pointTest 6 4096
    block64
    block65)
    (checkPow_join pointTest 6 4224
    block66
    block67))
    (checkPow_join pointTest 7 4352
    (checkPow_join pointTest 6 4352
    block68
    block69)
    (checkPow_join pointTest 6 4480
    block70
    block71)))
    (checkPow_join pointTest 8 4608
    (checkPow_join pointTest 7 4608
    (checkPow_join pointTest 6 4608
    block72
    block73)
    (checkPow_join pointTest 6 4736
    block74
    block75))
    (checkPow_join pointTest 7 4864
    (checkPow_join pointTest 6 4864
    block76
    block77)
    (checkPow_join pointTest 6 4992
    block78
    block79))))
    (checkPow_join pointTest 9 5120
    (checkPow_join pointTest 8 5120
    (checkPow_join pointTest 7 5120
    (checkPow_join pointTest 6 5120
    block80
    block81)
    (checkPow_join pointTest 6 5248
    block82
    block83))
    (checkPow_join pointTest 7 5376
    (checkPow_join pointTest 6 5376
    block84
    block85)
    (checkPow_join pointTest 6 5504
    block86
    block87)))
    (checkPow_join pointTest 8 5632
    (checkPow_join pointTest 7 5632
    (checkPow_join pointTest 6 5632
    block88
    block89)
    (checkPow_join pointTest 6 5760
    block90
    block91))
    (checkPow_join pointTest 7 5888
    (checkPow_join pointTest 6 5888
    block92
    block93)
    (checkPow_join pointTest 6 6016
    block94
    block95)))))
    (checkPow_join pointTest 10 6144
    (checkPow_join pointTest 9 6144
    (checkPow_join pointTest 8 6144
    (checkPow_join pointTest 7 6144
    (checkPow_join pointTest 6 6144
    block96
    block97)
    (checkPow_join pointTest 6 6272
    block98
    block99))
    (checkPow_join pointTest 7 6400
    (checkPow_join pointTest 6 6400
    block100
    block101)
    (checkPow_join pointTest 6 6528
    block102
    block103)))
    (checkPow_join pointTest 8 6656
    (checkPow_join pointTest 7 6656
    (checkPow_join pointTest 6 6656
    block104
    block105)
    (checkPow_join pointTest 6 6784
    block106
    block107))
    (checkPow_join pointTest 7 6912
    (checkPow_join pointTest 6 6912
    block108
    block109)
    (checkPow_join pointTest 6 7040
    block110
    block111))))
    (checkPow_join pointTest 9 7168
    (checkPow_join pointTest 8 7168
    (checkPow_join pointTest 7 7168
    (checkPow_join pointTest 6 7168
    block112
    block113)
    (checkPow_join pointTest 6 7296
    block114
    block115))
    (checkPow_join pointTest 7 7424
    (checkPow_join pointTest 6 7424
    block116
    block117)
    (checkPow_join pointTest 6 7552
    block118
    block119)))
    (checkPow_join pointTest 8 7680
    (checkPow_join pointTest 7 7680
    (checkPow_join pointTest 6 7680
    block120
    block121)
    (checkPow_join pointTest 6 7808
    block122
    block123))
    (checkPow_join pointTest 7 7936
    (checkPow_join pointTest 6 7936
    block124
    block125)
    (checkPow_join pointTest 6 8064
    block126
    block127))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
