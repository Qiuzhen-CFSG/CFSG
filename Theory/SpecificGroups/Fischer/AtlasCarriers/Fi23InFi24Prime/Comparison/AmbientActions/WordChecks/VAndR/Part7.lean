module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.WordChecks.VAndR.Check

/-!
# Forward v and r checks on the range starting at 28672

Each block checks 64 labels by kernel reduction. The balanced checker joins
these blocks to certify a range of 4096 consecutive indices. The last range
uses `Fin.ofNat` beyond 31670; those repeated labels do not affect coverage.

Source: the literal words and retained ATLAS tables described in `VAndR.Check`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR

-- Each reduction cache is released before the next declaration is elaborated.
set_option Elab.async false

private theorem block448 : checkPow pointTest 28672 6 = true := by
  decide +kernel

private theorem block449 : checkPow pointTest 28736 6 = true := by
  decide +kernel

private theorem block450 : checkPow pointTest 28800 6 = true := by
  decide +kernel

private theorem block451 : checkPow pointTest 28864 6 = true := by
  decide +kernel

private theorem block452 : checkPow pointTest 28928 6 = true := by
  decide +kernel

private theorem block453 : checkPow pointTest 28992 6 = true := by
  decide +kernel

private theorem block454 : checkPow pointTest 29056 6 = true := by
  decide +kernel

private theorem block455 : checkPow pointTest 29120 6 = true := by
  decide +kernel

private theorem block456 : checkPow pointTest 29184 6 = true := by
  decide +kernel

private theorem block457 : checkPow pointTest 29248 6 = true := by
  decide +kernel

private theorem block458 : checkPow pointTest 29312 6 = true := by
  decide +kernel

private theorem block459 : checkPow pointTest 29376 6 = true := by
  decide +kernel

private theorem block460 : checkPow pointTest 29440 6 = true := by
  decide +kernel

private theorem block461 : checkPow pointTest 29504 6 = true := by
  decide +kernel

private theorem block462 : checkPow pointTest 29568 6 = true := by
  decide +kernel

private theorem block463 : checkPow pointTest 29632 6 = true := by
  decide +kernel

private theorem block464 : checkPow pointTest 29696 6 = true := by
  decide +kernel

private theorem block465 : checkPow pointTest 29760 6 = true := by
  decide +kernel

private theorem block466 : checkPow pointTest 29824 6 = true := by
  decide +kernel

private theorem block467 : checkPow pointTest 29888 6 = true := by
  decide +kernel

private theorem block468 : checkPow pointTest 29952 6 = true := by
  decide +kernel

private theorem block469 : checkPow pointTest 30016 6 = true := by
  decide +kernel

private theorem block470 : checkPow pointTest 30080 6 = true := by
  decide +kernel

private theorem block471 : checkPow pointTest 30144 6 = true := by
  decide +kernel

private theorem block472 : checkPow pointTest 30208 6 = true := by
  decide +kernel

private theorem block473 : checkPow pointTest 30272 6 = true := by
  decide +kernel

private theorem block474 : checkPow pointTest 30336 6 = true := by
  decide +kernel

private theorem block475 : checkPow pointTest 30400 6 = true := by
  decide +kernel

private theorem block476 : checkPow pointTest 30464 6 = true := by
  decide +kernel

private theorem block477 : checkPow pointTest 30528 6 = true := by
  decide +kernel

private theorem block478 : checkPow pointTest 30592 6 = true := by
  decide +kernel

private theorem block479 : checkPow pointTest 30656 6 = true := by
  decide +kernel

private theorem block480 : checkPow pointTest 30720 6 = true := by
  decide +kernel

private theorem block481 : checkPow pointTest 30784 6 = true := by
  decide +kernel

private theorem block482 : checkPow pointTest 30848 6 = true := by
  decide +kernel

private theorem block483 : checkPow pointTest 30912 6 = true := by
  decide +kernel

private theorem block484 : checkPow pointTest 30976 6 = true := by
  decide +kernel

private theorem block485 : checkPow pointTest 31040 6 = true := by
  decide +kernel

private theorem block486 : checkPow pointTest 31104 6 = true := by
  decide +kernel

private theorem block487 : checkPow pointTest 31168 6 = true := by
  decide +kernel

private theorem block488 : checkPow pointTest 31232 6 = true := by
  decide +kernel

private theorem block489 : checkPow pointTest 31296 6 = true := by
  decide +kernel

private theorem block490 : checkPow pointTest 31360 6 = true := by
  decide +kernel

private theorem block491 : checkPow pointTest 31424 6 = true := by
  decide +kernel

private theorem block492 : checkPow pointTest 31488 6 = true := by
  decide +kernel

private theorem block493 : checkPow pointTest 31552 6 = true := by
  decide +kernel

private theorem block494 : checkPow pointTest 31616 6 = true := by
  decide +kernel

private theorem block495 : checkPow pointTest 31680 6 = true := by
  decide +kernel

private theorem block496 : checkPow pointTest 31744 6 = true := by
  decide +kernel

private theorem block497 : checkPow pointTest 31808 6 = true := by
  decide +kernel

private theorem block498 : checkPow pointTest 31872 6 = true := by
  decide +kernel

private theorem block499 : checkPow pointTest 31936 6 = true := by
  decide +kernel

private theorem block500 : checkPow pointTest 32000 6 = true := by
  decide +kernel

private theorem block501 : checkPow pointTest 32064 6 = true := by
  decide +kernel

private theorem block502 : checkPow pointTest 32128 6 = true := by
  decide +kernel

private theorem block503 : checkPow pointTest 32192 6 = true := by
  decide +kernel

private theorem block504 : checkPow pointTest 32256 6 = true := by
  decide +kernel

private theorem block505 : checkPow pointTest 32320 6 = true := by
  decide +kernel

private theorem block506 : checkPow pointTest 32384 6 = true := by
  decide +kernel

private theorem block507 : checkPow pointTest 32448 6 = true := by
  decide +kernel

private theorem block508 : checkPow pointTest 32512 6 = true := by
  decide +kernel

private theorem block509 : checkPow pointTest 32576 6 = true := by
  decide +kernel

private theorem block510 : checkPow pointTest 32640 6 = true := by
  decide +kernel

private theorem block511 : checkPow pointTest 32704 6 = true := by
  decide +kernel

/-- The two word actions on a complete 4096-index range. -/
theorem checked7 : checkPow pointTest 28672 12 = true :=
  (checkPow_join pointTest 11 28672
    (checkPow_join pointTest 10 28672
    (checkPow_join pointTest 9 28672
    (checkPow_join pointTest 8 28672
    (checkPow_join pointTest 7 28672
    (checkPow_join pointTest 6 28672
    block448
    block449)
    (checkPow_join pointTest 6 28800
    block450
    block451))
    (checkPow_join pointTest 7 28928
    (checkPow_join pointTest 6 28928
    block452
    block453)
    (checkPow_join pointTest 6 29056
    block454
    block455)))
    (checkPow_join pointTest 8 29184
    (checkPow_join pointTest 7 29184
    (checkPow_join pointTest 6 29184
    block456
    block457)
    (checkPow_join pointTest 6 29312
    block458
    block459))
    (checkPow_join pointTest 7 29440
    (checkPow_join pointTest 6 29440
    block460
    block461)
    (checkPow_join pointTest 6 29568
    block462
    block463))))
    (checkPow_join pointTest 9 29696
    (checkPow_join pointTest 8 29696
    (checkPow_join pointTest 7 29696
    (checkPow_join pointTest 6 29696
    block464
    block465)
    (checkPow_join pointTest 6 29824
    block466
    block467))
    (checkPow_join pointTest 7 29952
    (checkPow_join pointTest 6 29952
    block468
    block469)
    (checkPow_join pointTest 6 30080
    block470
    block471)))
    (checkPow_join pointTest 8 30208
    (checkPow_join pointTest 7 30208
    (checkPow_join pointTest 6 30208
    block472
    block473)
    (checkPow_join pointTest 6 30336
    block474
    block475))
    (checkPow_join pointTest 7 30464
    (checkPow_join pointTest 6 30464
    block476
    block477)
    (checkPow_join pointTest 6 30592
    block478
    block479)))))
    (checkPow_join pointTest 10 30720
    (checkPow_join pointTest 9 30720
    (checkPow_join pointTest 8 30720
    (checkPow_join pointTest 7 30720
    (checkPow_join pointTest 6 30720
    block480
    block481)
    (checkPow_join pointTest 6 30848
    block482
    block483))
    (checkPow_join pointTest 7 30976
    (checkPow_join pointTest 6 30976
    block484
    block485)
    (checkPow_join pointTest 6 31104
    block486
    block487)))
    (checkPow_join pointTest 8 31232
    (checkPow_join pointTest 7 31232
    (checkPow_join pointTest 6 31232
    block488
    block489)
    (checkPow_join pointTest 6 31360
    block490
    block491))
    (checkPow_join pointTest 7 31488
    (checkPow_join pointTest 6 31488
    block492
    block493)
    (checkPow_join pointTest 6 31616
    block494
    block495))))
    (checkPow_join pointTest 9 31744
    (checkPow_join pointTest 8 31744
    (checkPow_join pointTest 7 31744
    (checkPow_join pointTest 6 31744
    block496
    block497)
    (checkPow_join pointTest 6 31872
    block498
    block499))
    (checkPow_join pointTest 7 32000
    (checkPow_join pointTest 6 32000
    block500
    block501)
    (checkPow_join pointTest 6 32128
    block502
    block503)))
    (checkPow_join pointTest 8 32256
    (checkPow_join pointTest 7 32256
    (checkPow_join pointTest 6 32256
    block504
    block505)
    (checkPow_join pointTest 6 32384
    block506
    block507))
    (checkPow_join pointTest 7 32512
    (checkPow_join pointTest 6 32512
    block508
    block509)
    (checkPow_join pointTest 6 32640
    block510
    block511))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.WordChecks.VAndR
