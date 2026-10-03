module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC500To509
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC510To519
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC520To529
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC530To539
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC540To549
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC550To559
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC560To569
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC570To579
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC580To589
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperC590To599

/-!
# Maximal-subgroup classification for small even descent nodes 500–599

The individual finite certificates classify every maximal subgroup as contained
in the core, admitting an outside centralizer witness, or equal to a recorded
edge. Exhausting the indicated interval combines these kernel-checked results
without changing the original node or edge numbering.

Source: Shinoda (1975), (2.3), pp. 81–82, and the root-word conventions and
input provenance in `SmallEvenDescentEdgeData`.
-/

public section
namespace ReeTwo.SylowModel.SmallEvenUpperCertificates

/-- Classification of maximal subgroups for descent nodes 500 through 599. -/
theorem classified500To599 (i : Fin 600) (hi : 500 ≤ i.val)
    (H : Subgroup SylowModel) (h : H ⋖ smallEvenDescentNode i) : Classified H := by
  have hil := i.isLt
  interval_cases he : i.val
  · have heq : i = 500 := Fin.ext he
    subst i
    exact classified500 H h
  · have heq : i = 501 := Fin.ext he
    subst i
    exact classified501 H h
  · have heq : i = 502 := Fin.ext he
    subst i
    exact classified502 H h
  · have heq : i = 503 := Fin.ext he
    subst i
    exact classified503 H h
  · have heq : i = 504 := Fin.ext he
    subst i
    exact classified504 H h
  · have heq : i = 505 := Fin.ext he
    subst i
    exact classified505 H h
  · have heq : i = 506 := Fin.ext he
    subst i
    exact classified506 H h
  · have heq : i = 507 := Fin.ext he
    subst i
    exact classified507 H h
  · have heq : i = 508 := Fin.ext he
    subst i
    exact classified508 H h
  · have heq : i = 509 := Fin.ext he
    subst i
    exact classified509 H h
  · have heq : i = 510 := Fin.ext he
    subst i
    exact classified510 H h
  · have heq : i = 511 := Fin.ext he
    subst i
    exact classified511 H h
  · have heq : i = 512 := Fin.ext he
    subst i
    exact classified512 H h
  · have heq : i = 513 := Fin.ext he
    subst i
    exact classified513 H h
  · have heq : i = 514 := Fin.ext he
    subst i
    exact classified514 H h
  · have heq : i = 515 := Fin.ext he
    subst i
    exact classified515 H h
  · have heq : i = 516 := Fin.ext he
    subst i
    exact classified516 H h
  · have heq : i = 517 := Fin.ext he
    subst i
    exact classified517 H h
  · have heq : i = 518 := Fin.ext he
    subst i
    exact classified518 H h
  · have heq : i = 519 := Fin.ext he
    subst i
    exact classified519 H h
  · have heq : i = 520 := Fin.ext he
    subst i
    exact classified520 H h
  · have heq : i = 521 := Fin.ext he
    subst i
    exact classified521 H h
  · have heq : i = 522 := Fin.ext he
    subst i
    exact classified522 H h
  · have heq : i = 523 := Fin.ext he
    subst i
    exact classified523 H h
  · have heq : i = 524 := Fin.ext he
    subst i
    exact classified524 H h
  · have heq : i = 525 := Fin.ext he
    subst i
    exact classified525 H h
  · have heq : i = 526 := Fin.ext he
    subst i
    exact classified526 H h
  · have heq : i = 527 := Fin.ext he
    subst i
    exact classified527 H h
  · have heq : i = 528 := Fin.ext he
    subst i
    exact classified528 H h
  · have heq : i = 529 := Fin.ext he
    subst i
    exact classified529 H h
  · have heq : i = 530 := Fin.ext he
    subst i
    exact classified530 H h
  · have heq : i = 531 := Fin.ext he
    subst i
    exact classified531 H h
  · have heq : i = 532 := Fin.ext he
    subst i
    exact classified532 H h
  · have heq : i = 533 := Fin.ext he
    subst i
    exact classified533 H h
  · have heq : i = 534 := Fin.ext he
    subst i
    exact classified534 H h
  · have heq : i = 535 := Fin.ext he
    subst i
    exact classified535 H h
  · have heq : i = 536 := Fin.ext he
    subst i
    exact classified536 H h
  · have heq : i = 537 := Fin.ext he
    subst i
    exact classified537 H h
  · have heq : i = 538 := Fin.ext he
    subst i
    exact classified538 H h
  · have heq : i = 539 := Fin.ext he
    subst i
    exact classified539 H h
  · have heq : i = 540 := Fin.ext he
    subst i
    exact classified540 H h
  · have heq : i = 541 := Fin.ext he
    subst i
    exact classified541 H h
  · have heq : i = 542 := Fin.ext he
    subst i
    exact classified542 H h
  · have heq : i = 543 := Fin.ext he
    subst i
    exact classified543 H h
  · have heq : i = 544 := Fin.ext he
    subst i
    exact classified544 H h
  · have heq : i = 545 := Fin.ext he
    subst i
    exact classified545 H h
  · have heq : i = 546 := Fin.ext he
    subst i
    exact classified546 H h
  · have heq : i = 547 := Fin.ext he
    subst i
    exact classified547 H h
  · have heq : i = 548 := Fin.ext he
    subst i
    exact classified548 H h
  · have heq : i = 549 := Fin.ext he
    subst i
    exact classified549 H h
  · have heq : i = 550 := Fin.ext he
    subst i
    exact classified550 H h
  · have heq : i = 551 := Fin.ext he
    subst i
    exact classified551 H h
  · have heq : i = 552 := Fin.ext he
    subst i
    exact classified552 H h
  · have heq : i = 553 := Fin.ext he
    subst i
    exact classified553 H h
  · have heq : i = 554 := Fin.ext he
    subst i
    exact classified554 H h
  · have heq : i = 555 := Fin.ext he
    subst i
    exact classified555 H h
  · have heq : i = 556 := Fin.ext he
    subst i
    exact classified556 H h
  · have heq : i = 557 := Fin.ext he
    subst i
    exact classified557 H h
  · have heq : i = 558 := Fin.ext he
    subst i
    exact classified558 H h
  · have heq : i = 559 := Fin.ext he
    subst i
    exact classified559 H h
  · have heq : i = 560 := Fin.ext he
    subst i
    exact classified560 H h
  · have heq : i = 561 := Fin.ext he
    subst i
    exact classified561 H h
  · have heq : i = 562 := Fin.ext he
    subst i
    exact classified562 H h
  · have heq : i = 563 := Fin.ext he
    subst i
    exact classified563 H h
  · have heq : i = 564 := Fin.ext he
    subst i
    exact classified564 H h
  · have heq : i = 565 := Fin.ext he
    subst i
    exact classified565 H h
  · have heq : i = 566 := Fin.ext he
    subst i
    exact classified566 H h
  · have heq : i = 567 := Fin.ext he
    subst i
    exact classified567 H h
  · have heq : i = 568 := Fin.ext he
    subst i
    exact classified568 H h
  · have heq : i = 569 := Fin.ext he
    subst i
    exact classified569 H h
  · have heq : i = 570 := Fin.ext he
    subst i
    exact classified570 H h
  · have heq : i = 571 := Fin.ext he
    subst i
    exact classified571 H h
  · have heq : i = 572 := Fin.ext he
    subst i
    exact classified572 H h
  · have heq : i = 573 := Fin.ext he
    subst i
    exact classified573 H h
  · have heq : i = 574 := Fin.ext he
    subst i
    exact classified574 H h
  · have heq : i = 575 := Fin.ext he
    subst i
    exact classified575 H h
  · have heq : i = 576 := Fin.ext he
    subst i
    exact classified576 H h
  · have heq : i = 577 := Fin.ext he
    subst i
    exact classified577 H h
  · have heq : i = 578 := Fin.ext he
    subst i
    exact classified578 H h
  · have heq : i = 579 := Fin.ext he
    subst i
    exact classified579 H h
  · have heq : i = 580 := Fin.ext he
    subst i
    exact classified580 H h
  · have heq : i = 581 := Fin.ext he
    subst i
    exact classified581 H h
  · have heq : i = 582 := Fin.ext he
    subst i
    exact classified582 H h
  · have heq : i = 583 := Fin.ext he
    subst i
    exact classified583 H h
  · have heq : i = 584 := Fin.ext he
    subst i
    exact classified584 H h
  · have heq : i = 585 := Fin.ext he
    subst i
    exact classified585 H h
  · have heq : i = 586 := Fin.ext he
    subst i
    exact classified586 H h
  · have heq : i = 587 := Fin.ext he
    subst i
    exact classified587 H h
  · have heq : i = 588 := Fin.ext he
    subst i
    exact classified588 H h
  · have heq : i = 589 := Fin.ext he
    subst i
    exact classified589 H h
  · have heq : i = 590 := Fin.ext he
    subst i
    exact classified590 H h
  · have heq : i = 591 := Fin.ext he
    subst i
    exact classified591 H h
  · have heq : i = 592 := Fin.ext he
    subst i
    exact classified592 H h
  · have heq : i = 593 := Fin.ext he
    subst i
    exact classified593 H h
  · have heq : i = 594 := Fin.ext he
    subst i
    exact classified594 H h
  · have heq : i = 595 := Fin.ext he
    subst i
    exact classified595 H h
  · have heq : i = 596 := Fin.ext he
    subst i
    exact classified596 H h
  · have heq : i = 597 := Fin.ext he
    subst i
    exact classified597 H h
  · have heq : i = 598 := Fin.ext he
    subst i
    exact classified598 H h
  · have heq : i = 599 := Fin.ext he
    subst i
    exact classified599 H h

end ReeTwo.SylowModel.SmallEvenUpperCertificates
