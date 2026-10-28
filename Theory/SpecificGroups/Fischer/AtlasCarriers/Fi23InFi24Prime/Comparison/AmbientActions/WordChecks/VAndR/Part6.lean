module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 24576

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block384 : checkPow pointTest 24576 6 = true := by
  decide +kernel

private theorem block385 : checkPow pointTest 24640 6 = true := by
  decide +kernel

private theorem block386 : checkPow pointTest 24704 6 = true := by
  decide +kernel

private theorem block387 : checkPow pointTest 24768 6 = true := by
  decide +kernel

private theorem block388 : checkPow pointTest 24832 6 = true := by
  decide +kernel

private theorem block389 : checkPow pointTest 24896 6 = true := by
  decide +kernel

private theorem block390 : checkPow pointTest 24960 6 = true := by
  decide +kernel

private theorem block391 : checkPow pointTest 25024 6 = true := by
  decide +kernel

private theorem block392 : checkPow pointTest 25088 6 = true := by
  decide +kernel

private theorem block393 : checkPow pointTest 25152 6 = true := by
  decide +kernel

private theorem block394 : checkPow pointTest 25216 6 = true := by
  decide +kernel

private theorem block395 : checkPow pointTest 25280 6 = true := by
  decide +kernel

private theorem block396 : checkPow pointTest 25344 6 = true := by
  decide +kernel

private theorem block397 : checkPow pointTest 25408 6 = true := by
  decide +kernel

private theorem block398 : checkPow pointTest 25472 6 = true := by
  decide +kernel

private theorem block399 : checkPow pointTest 25536 6 = true := by
  decide +kernel

private theorem block400 : checkPow pointTest 25600 6 = true := by
  decide +kernel

private theorem block401 : checkPow pointTest 25664 6 = true := by
  decide +kernel

private theorem block402 : checkPow pointTest 25728 6 = true := by
  decide +kernel

private theorem block403 : checkPow pointTest 25792 6 = true := by
  decide +kernel

private theorem block404 : checkPow pointTest 25856 6 = true := by
  decide +kernel

private theorem block405 : checkPow pointTest 25920 6 = true := by
  decide +kernel

private theorem block406 : checkPow pointTest 25984 6 = true := by
  decide +kernel

private theorem block407 : checkPow pointTest 26048 6 = true := by
  decide +kernel

private theorem block408 : checkPow pointTest 26112 6 = true := by
  decide +kernel

private theorem block409 : checkPow pointTest 26176 6 = true := by
  decide +kernel

private theorem block410 : checkPow pointTest 26240 6 = true := by
  decide +kernel

private theorem block411 : checkPow pointTest 26304 6 = true := by
  decide +kernel

private theorem block412 : checkPow pointTest 26368 6 = true := by
  decide +kernel

private theorem block413 : checkPow pointTest 26432 6 = true := by
  decide +kernel

private theorem block414 : checkPow pointTest 26496 6 = true := by
  decide +kernel

private theorem block415 : checkPow pointTest 26560 6 = true := by
  decide +kernel

private theorem block416 : checkPow pointTest 26624 6 = true := by
  decide +kernel

private theorem block417 : checkPow pointTest 26688 6 = true := by
  decide +kernel

private theorem block418 : checkPow pointTest 26752 6 = true := by
  decide +kernel

private theorem block419 : checkPow pointTest 26816 6 = true := by
  decide +kernel

private theorem block420 : checkPow pointTest 26880 6 = true := by
  decide +kernel

private theorem block421 : checkPow pointTest 26944 6 = true := by
  decide +kernel

private theorem block422 : checkPow pointTest 27008 6 = true := by
  decide +kernel

private theorem block423 : checkPow pointTest 27072 6 = true := by
  decide +kernel

private theorem block424 : checkPow pointTest 27136 6 = true := by
  decide +kernel

private theorem block425 : checkPow pointTest 27200 6 = true := by
  decide +kernel

private theorem block426 : checkPow pointTest 27264 6 = true := by
  decide +kernel

private theorem block427 : checkPow pointTest 27328 6 = true := by
  decide +kernel

private theorem block428 : checkPow pointTest 27392 6 = true := by
  decide +kernel

private theorem block429 : checkPow pointTest 27456 6 = true := by
  decide +kernel

private theorem block430 : checkPow pointTest 27520 6 = true := by
  decide +kernel

private theorem block431 : checkPow pointTest 27584 6 = true := by
  decide +kernel

private theorem block432 : checkPow pointTest 27648 6 = true := by
  decide +kernel

private theorem block433 : checkPow pointTest 27712 6 = true := by
  decide +kernel

private theorem block434 : checkPow pointTest 27776 6 = true := by
  decide +kernel

private theorem block435 : checkPow pointTest 27840 6 = true := by
  decide +kernel

private theorem block436 : checkPow pointTest 27904 6 = true := by
  decide +kernel

private theorem block437 : checkPow pointTest 27968 6 = true := by
  decide +kernel

private theorem block438 : checkPow pointTest 28032 6 = true := by
  decide +kernel

private theorem block439 : checkPow pointTest 28096 6 = true := by
  decide +kernel

private theorem block440 : checkPow pointTest 28160 6 = true := by
  decide +kernel

private theorem block441 : checkPow pointTest 28224 6 = true := by
  decide +kernel

private theorem block442 : checkPow pointTest 28288 6 = true := by
  decide +kernel

private theorem block443 : checkPow pointTest 28352 6 = true := by
  decide +kernel

private theorem block444 : checkPow pointTest 28416 6 = true := by
  decide +kernel

private theorem block445 : checkPow pointTest 28480 6 = true := by
  decide +kernel

private theorem block446 : checkPow pointTest 28544 6 = true := by
  decide +kernel

private theorem block447 : checkPow pointTest 28608 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked6 : checkPow pointTest 24576 12 = true :=
  (checkPow_join pointTest 11 24576
    (checkPow_join pointTest 10 24576
    (checkPow_join pointTest 9 24576
    (checkPow_join pointTest 8 24576
    (checkPow_join pointTest 7 24576
    (checkPow_join pointTest 6 24576
    block384
    block385)
    (checkPow_join pointTest 6 24704
    block386
    block387))
    (checkPow_join pointTest 7 24832
    (checkPow_join pointTest 6 24832
    block388
    block389)
    (checkPow_join pointTest 6 24960
    block390
    block391)))
    (checkPow_join pointTest 8 25088
    (checkPow_join pointTest 7 25088
    (checkPow_join pointTest 6 25088
    block392
    block393)
    (checkPow_join pointTest 6 25216
    block394
    block395))
    (checkPow_join pointTest 7 25344
    (checkPow_join pointTest 6 25344
    block396
    block397)
    (checkPow_join pointTest 6 25472
    block398
    block399))))
    (checkPow_join pointTest 9 25600
    (checkPow_join pointTest 8 25600
    (checkPow_join pointTest 7 25600
    (checkPow_join pointTest 6 25600
    block400
    block401)
    (checkPow_join pointTest 6 25728
    block402
    block403))
    (checkPow_join pointTest 7 25856
    (checkPow_join pointTest 6 25856
    block404
    block405)
    (checkPow_join pointTest 6 25984
    block406
    block407)))
    (checkPow_join pointTest 8 26112
    (checkPow_join pointTest 7 26112
    (checkPow_join pointTest 6 26112
    block408
    block409)
    (checkPow_join pointTest 6 26240
    block410
    block411))
    (checkPow_join pointTest 7 26368
    (checkPow_join pointTest 6 26368
    block412
    block413)
    (checkPow_join pointTest 6 26496
    block414
    block415)))))
    (checkPow_join pointTest 10 26624
    (checkPow_join pointTest 9 26624
    (checkPow_join pointTest 8 26624
    (checkPow_join pointTest 7 26624
    (checkPow_join pointTest 6 26624
    block416
    block417)
    (checkPow_join pointTest 6 26752
    block418
    block419))
    (checkPow_join pointTest 7 26880
    (checkPow_join pointTest 6 26880
    block420
    block421)
    (checkPow_join pointTest 6 27008
    block422
    block423)))
    (checkPow_join pointTest 8 27136
    (checkPow_join pointTest 7 27136
    (checkPow_join pointTest 6 27136
    block424
    block425)
    (checkPow_join pointTest 6 27264
    block426
    block427))
    (checkPow_join pointTest 7 27392
    (checkPow_join pointTest 6 27392
    block428
    block429)
    (checkPow_join pointTest 6 27520
    block430
    block431))))
    (checkPow_join pointTest 9 27648
    (checkPow_join pointTest 8 27648
    (checkPow_join pointTest 7 27648
    (checkPow_join pointTest 6 27648
    block432
    block433)
    (checkPow_join pointTest 6 27776
    block434
    block435))
    (checkPow_join pointTest 7 27904
    (checkPow_join pointTest 6 27904
    block436
    block437)
    (checkPow_join pointTest 6 28032
    block438
    block439)))
    (checkPow_join pointTest 8 28160
    (checkPow_join pointTest 7 28160
    (checkPow_join pointTest 6 28160
    block440
    block441)
    (checkPow_join pointTest 6 28288
    block442
    block443))
    (checkPow_join pointTest 7 28416
    (checkPow_join pointTest 6 28416
    block444
    block445)
    (checkPow_join pointTest 6 28544
    block446
    block447))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
