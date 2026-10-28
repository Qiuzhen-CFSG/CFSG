module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 20480

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block320 : checkPow pointTest 20480 6 = true := by
  decide +kernel

private theorem block321 : checkPow pointTest 20544 6 = true := by
  decide +kernel

private theorem block322 : checkPow pointTest 20608 6 = true := by
  decide +kernel

private theorem block323 : checkPow pointTest 20672 6 = true := by
  decide +kernel

private theorem block324 : checkPow pointTest 20736 6 = true := by
  decide +kernel

private theorem block325 : checkPow pointTest 20800 6 = true := by
  decide +kernel

private theorem block326 : checkPow pointTest 20864 6 = true := by
  decide +kernel

private theorem block327 : checkPow pointTest 20928 6 = true := by
  decide +kernel

private theorem block328 : checkPow pointTest 20992 6 = true := by
  decide +kernel

private theorem block329 : checkPow pointTest 21056 6 = true := by
  decide +kernel

private theorem block330 : checkPow pointTest 21120 6 = true := by
  decide +kernel

private theorem block331 : checkPow pointTest 21184 6 = true := by
  decide +kernel

private theorem block332 : checkPow pointTest 21248 6 = true := by
  decide +kernel

private theorem block333 : checkPow pointTest 21312 6 = true := by
  decide +kernel

private theorem block334 : checkPow pointTest 21376 6 = true := by
  decide +kernel

private theorem block335 : checkPow pointTest 21440 6 = true := by
  decide +kernel

private theorem block336 : checkPow pointTest 21504 6 = true := by
  decide +kernel

private theorem block337 : checkPow pointTest 21568 6 = true := by
  decide +kernel

private theorem block338 : checkPow pointTest 21632 6 = true := by
  decide +kernel

private theorem block339 : checkPow pointTest 21696 6 = true := by
  decide +kernel

private theorem block340 : checkPow pointTest 21760 6 = true := by
  decide +kernel

private theorem block341 : checkPow pointTest 21824 6 = true := by
  decide +kernel

private theorem block342 : checkPow pointTest 21888 6 = true := by
  decide +kernel

private theorem block343 : checkPow pointTest 21952 6 = true := by
  decide +kernel

private theorem block344 : checkPow pointTest 22016 6 = true := by
  decide +kernel

private theorem block345 : checkPow pointTest 22080 6 = true := by
  decide +kernel

private theorem block346 : checkPow pointTest 22144 6 = true := by
  decide +kernel

private theorem block347 : checkPow pointTest 22208 6 = true := by
  decide +kernel

private theorem block348 : checkPow pointTest 22272 6 = true := by
  decide +kernel

private theorem block349 : checkPow pointTest 22336 6 = true := by
  decide +kernel

private theorem block350 : checkPow pointTest 22400 6 = true := by
  decide +kernel

private theorem block351 : checkPow pointTest 22464 6 = true := by
  decide +kernel

private theorem block352 : checkPow pointTest 22528 6 = true := by
  decide +kernel

private theorem block353 : checkPow pointTest 22592 6 = true := by
  decide +kernel

private theorem block354 : checkPow pointTest 22656 6 = true := by
  decide +kernel

private theorem block355 : checkPow pointTest 22720 6 = true := by
  decide +kernel

private theorem block356 : checkPow pointTest 22784 6 = true := by
  decide +kernel

private theorem block357 : checkPow pointTest 22848 6 = true := by
  decide +kernel

private theorem block358 : checkPow pointTest 22912 6 = true := by
  decide +kernel

private theorem block359 : checkPow pointTest 22976 6 = true := by
  decide +kernel

private theorem block360 : checkPow pointTest 23040 6 = true := by
  decide +kernel

private theorem block361 : checkPow pointTest 23104 6 = true := by
  decide +kernel

private theorem block362 : checkPow pointTest 23168 6 = true := by
  decide +kernel

private theorem block363 : checkPow pointTest 23232 6 = true := by
  decide +kernel

private theorem block364 : checkPow pointTest 23296 6 = true := by
  decide +kernel

private theorem block365 : checkPow pointTest 23360 6 = true := by
  decide +kernel

private theorem block366 : checkPow pointTest 23424 6 = true := by
  decide +kernel

private theorem block367 : checkPow pointTest 23488 6 = true := by
  decide +kernel

private theorem block368 : checkPow pointTest 23552 6 = true := by
  decide +kernel

private theorem block369 : checkPow pointTest 23616 6 = true := by
  decide +kernel

private theorem block370 : checkPow pointTest 23680 6 = true := by
  decide +kernel

private theorem block371 : checkPow pointTest 23744 6 = true := by
  decide +kernel

private theorem block372 : checkPow pointTest 23808 6 = true := by
  decide +kernel

private theorem block373 : checkPow pointTest 23872 6 = true := by
  decide +kernel

private theorem block374 : checkPow pointTest 23936 6 = true := by
  decide +kernel

private theorem block375 : checkPow pointTest 24000 6 = true := by
  decide +kernel

private theorem block376 : checkPow pointTest 24064 6 = true := by
  decide +kernel

private theorem block377 : checkPow pointTest 24128 6 = true := by
  decide +kernel

private theorem block378 : checkPow pointTest 24192 6 = true := by
  decide +kernel

private theorem block379 : checkPow pointTest 24256 6 = true := by
  decide +kernel

private theorem block380 : checkPow pointTest 24320 6 = true := by
  decide +kernel

private theorem block381 : checkPow pointTest 24384 6 = true := by
  decide +kernel

private theorem block382 : checkPow pointTest 24448 6 = true := by
  decide +kernel

private theorem block383 : checkPow pointTest 24512 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked5 : checkPow pointTest 20480 12 = true :=
  (checkPow_join pointTest 11 20480
    (checkPow_join pointTest 10 20480
    (checkPow_join pointTest 9 20480
    (checkPow_join pointTest 8 20480
    (checkPow_join pointTest 7 20480
    (checkPow_join pointTest 6 20480
    block320
    block321)
    (checkPow_join pointTest 6 20608
    block322
    block323))
    (checkPow_join pointTest 7 20736
    (checkPow_join pointTest 6 20736
    block324
    block325)
    (checkPow_join pointTest 6 20864
    block326
    block327)))
    (checkPow_join pointTest 8 20992
    (checkPow_join pointTest 7 20992
    (checkPow_join pointTest 6 20992
    block328
    block329)
    (checkPow_join pointTest 6 21120
    block330
    block331))
    (checkPow_join pointTest 7 21248
    (checkPow_join pointTest 6 21248
    block332
    block333)
    (checkPow_join pointTest 6 21376
    block334
    block335))))
    (checkPow_join pointTest 9 21504
    (checkPow_join pointTest 8 21504
    (checkPow_join pointTest 7 21504
    (checkPow_join pointTest 6 21504
    block336
    block337)
    (checkPow_join pointTest 6 21632
    block338
    block339))
    (checkPow_join pointTest 7 21760
    (checkPow_join pointTest 6 21760
    block340
    block341)
    (checkPow_join pointTest 6 21888
    block342
    block343)))
    (checkPow_join pointTest 8 22016
    (checkPow_join pointTest 7 22016
    (checkPow_join pointTest 6 22016
    block344
    block345)
    (checkPow_join pointTest 6 22144
    block346
    block347))
    (checkPow_join pointTest 7 22272
    (checkPow_join pointTest 6 22272
    block348
    block349)
    (checkPow_join pointTest 6 22400
    block350
    block351)))))
    (checkPow_join pointTest 10 22528
    (checkPow_join pointTest 9 22528
    (checkPow_join pointTest 8 22528
    (checkPow_join pointTest 7 22528
    (checkPow_join pointTest 6 22528
    block352
    block353)
    (checkPow_join pointTest 6 22656
    block354
    block355))
    (checkPow_join pointTest 7 22784
    (checkPow_join pointTest 6 22784
    block356
    block357)
    (checkPow_join pointTest 6 22912
    block358
    block359)))
    (checkPow_join pointTest 8 23040
    (checkPow_join pointTest 7 23040
    (checkPow_join pointTest 6 23040
    block360
    block361)
    (checkPow_join pointTest 6 23168
    block362
    block363))
    (checkPow_join pointTest 7 23296
    (checkPow_join pointTest 6 23296
    block364
    block365)
    (checkPow_join pointTest 6 23424
    block366
    block367))))
    (checkPow_join pointTest 9 23552
    (checkPow_join pointTest 8 23552
    (checkPow_join pointTest 7 23552
    (checkPow_join pointTest 6 23552
    block368
    block369)
    (checkPow_join pointTest 6 23680
    block370
    block371))
    (checkPow_join pointTest 7 23808
    (checkPow_join pointTest 6 23808
    block372
    block373)
    (checkPow_join pointTest 6 23936
    block374
    block375)))
    (checkPow_join pointTest 8 24064
    (checkPow_join pointTest 7 24064
    (checkPow_join pointTest 6 24064
    block376
    block377)
    (checkPow_join pointTest 6 24192
    block378
    block379))
    (checkPow_join pointTest 7 24320
    (checkPow_join pointTest 6 24320
    block380
    block381)
    (checkPow_join pointTest 6 24448
    block382
    block383))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
