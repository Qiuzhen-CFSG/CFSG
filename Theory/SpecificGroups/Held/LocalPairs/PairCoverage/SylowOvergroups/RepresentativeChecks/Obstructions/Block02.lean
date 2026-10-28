module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 512 through 767

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_0512 : HasPrimeObstruction (representative 512) := by
  apply obstruction_of_cachedAction 512 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0513 : HasPrimeObstruction (representative 513) := by
  apply obstruction_of_cachedAction 513 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0514 : HasPrimeObstruction (representative 514) := by
  apply obstruction_of_cachedAction 514 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0515 : HasPrimeObstruction (representative 515) := by
  apply obstruction_of_cachedAction 515 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0516 : HasPrimeObstruction (representative 516) := by
  apply obstruction_of_cachedAction 516 [5, 2] 7 1
    (by decide) (by decide) (by decide) 73
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0517 : HasPrimeObstruction (representative 517) := by
  apply obstruction_of_cachedAction 517 [5] 7 1
    (by decide) (by decide) (by decide) 49
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0518 : HasPrimeObstruction (representative 518) := by
  apply obstruction_of_cachedAction 518 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0519 : HasPrimeObstruction (representative 519) := by
  apply obstruction_of_cachedAction 519 [5, 1] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0520 : HasPrimeObstruction (representative 520) := by
  apply obstruction_of_cachedAction 520 [5] 5 1
    (by decide) (by decide) (by decide) 43
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0521 : HasPrimeObstruction (representative 521) := by
  apply obstruction_of_cachedAction 521 [5, 1] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0522 : HasPrimeObstruction (representative 522) := by
  apply obstruction_of_cachedAction 522 [5, 2] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0523 : HasPrimeObstruction (representative 523) := by
  apply obstruction_of_cachedAction 523 [5, 1] 7 1
    (by decide) (by decide) (by decide) 76
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0524 : HasPrimeObstruction (representative 524) := by
  apply obstruction_of_cachedAction 524 [5] 7 1
    (by decide) (by decide) (by decide) 196
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0525 : HasPrimeObstruction (representative 525) := by
  apply obstruction_of_cachedAction 525 [5, 1] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0526 : HasPrimeObstruction (representative 526) := by
  apply obstruction_of_cachedAction 526 [5, 1] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0527 : HasPrimeObstruction (representative 527) := by
  apply obstruction_of_cachedAction 527 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0528 : HasPrimeObstruction (representative 528) := by
  apply obstruction_of_cachedAction 528 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0529 : HasPrimeObstruction (representative 529) := by
  apply obstruction_of_cachedAction 529 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0530 : HasPrimeObstruction (representative 530) := by
  apply obstruction_of_cachedAction 530 [5, 4] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0531 : HasPrimeObstruction (representative 531) := by
  apply obstruction_of_cachedAction 531 [5, 2] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0532 : HasPrimeObstruction (representative 532) := by
  apply obstruction_of_cachedAction 532 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0533 : HasPrimeObstruction (representative 533) := by
  apply obstruction_of_cachedAction 533 [5, 2] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0534 : HasPrimeObstruction (representative 534) := by
  apply obstruction_of_cachedAction 534 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0535 : HasPrimeObstruction (representative 535) := by
  apply obstruction_of_cachedAction 535 [5, 3] 5 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0536 : HasPrimeObstruction (representative 536) := by
  apply obstruction_of_cachedAction 536 [5, 4] 5 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0537 : HasPrimeObstruction (representative 537) := by
  apply obstruction_of_cachedAction 537 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0538 : HasPrimeObstruction (representative 538) := by
  apply obstruction_of_cachedAction 538 [5, 1] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0539 : HasPrimeObstruction (representative 539) := by
  apply obstruction_of_cachedAction 539 [5, 3] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0540 : HasPrimeObstruction (representative 540) := by
  apply obstruction_of_cachedAction 540 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0541 : HasPrimeObstruction (representative 541) := by
  apply obstruction_of_cachedAction 541 [5, 1] 7 1
    (by decide) (by decide) (by decide) 190
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0542 : HasPrimeObstruction (representative 542) := by
  apply obstruction_of_cachedAction 542 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0543 : HasPrimeObstruction (representative 543) := by
  apply obstruction_of_cachedAction 543 [5, 2] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0544 : HasPrimeObstruction (representative 544) := by
  apply obstruction_of_cachedAction 544 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0545 : HasPrimeObstruction (representative 545) := by
  apply obstruction_of_cachedAction 545 [5, 1] 7 1
    (by decide) (by decide) (by decide) 122
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0546 : HasPrimeObstruction (representative 546) := by
  apply obstruction_of_cachedAction 546 [5, 1] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0547 : HasPrimeObstruction (representative 547) := by
  apply obstruction_of_cachedAction 547 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0548 : HasPrimeObstruction (representative 548) := by
  apply obstruction_of_cachedAction 548 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0549 : HasPrimeObstruction (representative 549) := by
  apply obstruction_of_cachedAction 549 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0550 : HasPrimeObstruction (representative 550) := by
  apply obstruction_of_cachedAction 550 [5] 7 1
    (by decide) (by decide) (by decide) 94
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0551 : HasPrimeObstruction (representative 551) := by
  apply obstruction_of_cachedAction 551 [5] 7 1
    (by decide) (by decide) (by decide) 69
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0552 : HasPrimeObstruction (representative 552) := by
  apply obstruction_of_cachedAction 552 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0553 : HasPrimeObstruction (representative 553) := by
  apply obstruction_of_cachedAction 553 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0554 : HasPrimeObstruction (representative 554) := by
  apply obstruction_of_cachedAction 554 [5, 4] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0555 : HasPrimeObstruction (representative 555) := by
  apply obstruction_of_cachedAction 555 [5, 4] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0556 : HasPrimeObstruction (representative 556) := by
  apply obstruction_of_cachedAction 556 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0557 : HasPrimeObstruction (representative 557) := by
  apply obstruction_of_cachedAction 557 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0558 : HasPrimeObstruction (representative 558) := by
  apply obstruction_of_cachedAction 558 [5, 3] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0559 : HasPrimeObstruction (representative 559) := by
  apply obstruction_of_cachedAction 559 [5, 1] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0560 : HasPrimeObstruction (representative 560) := by
  apply obstruction_of_cachedAction 560 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0561 : HasPrimeObstruction (representative 561) := by
  apply obstruction_of_cachedAction 561 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0562 : HasPrimeObstruction (representative 562) := by
  apply obstruction_of_cachedAction 562 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0563 : HasPrimeObstruction (representative 563) := by
  apply obstruction_of_cachedAction 563 [5] 7 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0564 : HasPrimeObstruction (representative 564) := by
  apply obstruction_of_cachedAction 564 [5, 1] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0565 : HasPrimeObstruction (representative 565) := by
  apply obstruction_of_cachedAction 565 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0566 : HasPrimeObstruction (representative 566) := by
  apply obstruction_of_cachedAction 566 [5] 7 1
    (by decide) (by decide) (by decide) 63
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0567 : HasPrimeObstruction (representative 567) := by
  apply obstruction_of_cachedAction 567 [5, 2] 5 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0568 : HasPrimeObstruction (representative 568) := by
  apply obstruction_of_cachedAction 568 [5] 7 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0569 : HasPrimeObstruction (representative 569) := by
  apply obstruction_of_cachedAction 569 [5] 5 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0570 : HasPrimeObstruction (representative 570) := by
  apply obstruction_of_cachedAction 570 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0571 : HasPrimeObstruction (representative 571) := by
  apply obstruction_of_cachedAction 571 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0572 : HasPrimeObstruction (representative 572) := by
  apply obstruction_of_cachedAction 572 [5] 7 1
    (by decide) (by decide) (by decide) 75
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0573 : HasPrimeObstruction (representative 573) := by
  apply obstruction_of_cachedAction 573 [5, 4] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0574 : HasPrimeObstruction (representative 574) := by
  apply obstruction_of_cachedAction 574 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0575 : HasPrimeObstruction (representative 575) := by
  apply obstruction_of_cachedAction 575 [5] 7 1
    (by decide) (by decide) (by decide) 251
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0576 : HasPrimeObstruction (representative 576) := by
  apply obstruction_of_cachedAction 576 [5] 7 1
    (by decide) (by decide) (by decide) 270
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0577 : HasPrimeObstruction (representative 577) := by
  apply obstruction_of_cachedAction 577 [5] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0578 : HasPrimeObstruction (representative 578) := by
  apply obstruction_of_cachedAction 578 [5] 5 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0579 : HasPrimeObstruction (representative 579) := by
  apply obstruction_of_cachedAction 579 [5, 2] 7 1
    (by decide) (by decide) (by decide) 297
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0580 : HasPrimeObstruction (representative 580) := by
  apply obstruction_of_cachedAction 580 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0581 : HasPrimeObstruction (representative 581) := by
  apply obstruction_of_cachedAction 581 [5, 1] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0582 : HasPrimeObstruction (representative 582) := by
  apply obstruction_of_cachedAction 582 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0583 : HasPrimeObstruction (representative 583) := by
  apply obstruction_of_cachedAction 583 [5] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0584 : HasPrimeObstruction (representative 584) := by
  apply obstruction_of_cachedAction 584 [5, 1] 7 1
    (by decide) (by decide) (by decide) 157
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0585 : HasPrimeObstruction (representative 585) := by
  apply obstruction_of_cachedAction 585 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0586 : HasPrimeObstruction (representative 586) := by
  apply obstruction_of_cachedAction 586 [5] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0587 : HasPrimeObstruction (representative 587) := by
  apply obstruction_of_cachedAction 587 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0588 : HasPrimeObstruction (representative 588) := by
  apply obstruction_of_cachedAction 588 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0589 : HasPrimeObstruction (representative 589) := by
  apply obstruction_of_cachedAction 589 [5, 3] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0590 : HasPrimeObstruction (representative 590) := by
  apply obstruction_of_cachedAction 590 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0591 : HasPrimeObstruction (representative 591) := by
  apply obstruction_of_cachedAction 591 [5] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0592 : HasPrimeObstruction (representative 592) := by
  apply obstruction_of_cachedAction 592 [5, 1] 7 1
    (by decide) (by decide) (by decide) 90
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0593 : HasPrimeObstruction (representative 593) := by
  apply obstruction_of_cachedAction 593 [5, 1] 7 1
    (by decide) (by decide) (by decide) 92
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0594 : HasPrimeObstruction (representative 594) := by
  apply obstruction_of_cachedAction 594 [5, 2] 7 1
    (by decide) (by decide) (by decide) 84
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0595 : HasPrimeObstruction (representative 595) := by
  apply obstruction_of_cachedAction 595 [5, 1] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0596 : HasPrimeObstruction (representative 596) := by
  apply obstruction_of_cachedAction 596 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0597 : HasPrimeObstruction (representative 597) := by
  apply obstruction_of_cachedAction 597 [5, 3] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0598 : HasPrimeObstruction (representative 598) := by
  apply obstruction_of_cachedAction 598 [5, 1] 7 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0599 : HasPrimeObstruction (representative 599) := by
  apply obstruction_of_cachedAction 599 [5, 4] 5 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0600 : HasPrimeObstruction (representative 600) := by
  apply obstruction_of_cachedAction 600 [5, 2] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0601 : HasPrimeObstruction (representative 601) := by
  apply obstruction_of_cachedAction 601 [5] 5 1
    (by decide) (by decide) (by decide) 105
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0602 : HasPrimeObstruction (representative 602) := by
  apply obstruction_of_cachedAction 602 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0603 : HasPrimeObstruction (representative 603) := by
  apply obstruction_of_cachedAction 603 [5] 7 1
    (by decide) (by decide) (by decide) 174
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0604 : HasPrimeObstruction (representative 604) := by
  apply obstruction_of_cachedAction 604 [5, 3] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0605 : HasPrimeObstruction (representative 605) := by
  apply obstruction_of_cachedAction 605 [5, 4] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0606 : HasPrimeObstruction (representative 606) := by
  apply obstruction_of_cachedAction 606 [5] 7 1
    (by decide) (by decide) (by decide) 98
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0607 : HasPrimeObstruction (representative 607) := by
  apply obstruction_of_cachedAction 607 [5, 1] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0608 : HasPrimeObstruction (representative 608) := by
  apply obstruction_of_cachedAction 608 [5, 1] 7 1
    (by decide) (by decide) (by decide) 102
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0609 : HasPrimeObstruction (representative 609) := by
  apply obstruction_of_cachedAction 609 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0610 : HasPrimeObstruction (representative 610) := by
  apply obstruction_of_cachedAction 610 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0611 : HasPrimeObstruction (representative 611) := by
  apply obstruction_of_cachedAction 611 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0612 : HasPrimeObstruction (representative 612) := by
  apply obstruction_of_cachedAction 612 [5, 4] 5 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0613 : HasPrimeObstruction (representative 613) := by
  apply obstruction_of_cachedAction 613 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0614 : HasPrimeObstruction (representative 614) := by
  apply obstruction_of_cachedAction 614 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0615 : HasPrimeObstruction (representative 615) := by
  apply obstruction_of_cachedAction 615 [5, 3] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0616 : HasPrimeObstruction (representative 616) := by
  apply obstruction_of_cachedAction 616 [5, 2] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0617 : HasPrimeObstruction (representative 617) := by
  apply obstruction_of_cachedAction 617 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0618 : HasPrimeObstruction (representative 618) := by
  apply obstruction_of_cachedAction 618 [5] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0619 : HasPrimeObstruction (representative 619) := by
  apply obstruction_of_cachedAction 619 [5] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0620 : HasPrimeObstruction (representative 620) := by
  apply obstruction_of_cachedAction 620 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0621 : HasPrimeObstruction (representative 621) := by
  apply obstruction_of_cachedAction 621 [5, 2] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0622 : HasPrimeObstruction (representative 622) := by
  apply obstruction_of_cachedAction 622 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0623 : HasPrimeObstruction (representative 623) := by
  apply obstruction_of_cachedAction 623 [5] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0624 : HasPrimeObstruction (representative 624) := by
  apply obstruction_of_cachedAction 624 [5, 2] 5 1
    (by decide) (by decide) (by decide) 83
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0625 : HasPrimeObstruction (representative 625) := by
  apply obstruction_of_cachedAction 625 [5, 1] 5 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0626 : HasPrimeObstruction (representative 626) := by
  apply obstruction_of_cachedAction 626 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0627 : HasPrimeObstruction (representative 627) := by
  apply obstruction_of_cachedAction 627 [5] 5 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0628 : HasPrimeObstruction (representative 628) := by
  apply obstruction_of_cachedAction 628 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0629 : HasPrimeObstruction (representative 629) := by
  apply obstruction_of_cachedAction 629 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0630 : HasPrimeObstruction (representative 630) := by
  apply obstruction_of_cachedAction 630 [5] 5 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0631 : HasPrimeObstruction (representative 631) := by
  apply obstruction_of_cachedAction 631 [5, 2] 5 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0632 : HasPrimeObstruction (representative 632) := by
  apply obstruction_of_cachedAction 632 [5] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0633 : HasPrimeObstruction (representative 633) := by
  apply obstruction_of_cachedAction 633 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0634 : HasPrimeObstruction (representative 634) := by
  apply obstruction_of_cachedAction 634 [5, 3] 5 1
    (by decide) (by decide) (by decide) 49
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0635 : HasPrimeObstruction (representative 635) := by
  apply obstruction_of_cachedAction 635 [5] 5 1
    (by decide) (by decide) (by decide) 48
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0636 : HasPrimeObstruction (representative 636) := by
  apply obstruction_of_cachedAction 636 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0637 : HasPrimeObstruction (representative 637) := by
  apply obstruction_of_cachedAction 637 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0638 : HasPrimeObstruction (representative 638) := by
  apply obstruction_of_cachedAction 638 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0639 : HasPrimeObstruction (representative 639) := by
  apply obstruction_of_cachedAction 639 [5, 1] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0640 : HasPrimeObstruction (representative 640) := by
  apply obstruction_of_cachedAction 640 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0641 : HasPrimeObstruction (representative 641) := by
  apply obstruction_of_cachedAction 641 [5, 2] 5 1
    (by decide) (by decide) (by decide) 145
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0642 : HasPrimeObstruction (representative 642) := by
  apply obstruction_of_cachedAction 642 [5] 5 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0643 : HasPrimeObstruction (representative 643) := by
  apply obstruction_of_cachedAction 643 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0644 : HasPrimeObstruction (representative 644) := by
  apply obstruction_of_cachedAction 644 [5, 4] 5 1
    (by decide) (by decide) (by decide) 159
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0645 : HasPrimeObstruction (representative 645) := by
  apply obstruction_of_cachedAction 645 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0646 : HasPrimeObstruction (representative 646) := by
  apply obstruction_of_cachedAction 646 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0647 : HasPrimeObstruction (representative 647) := by
  apply obstruction_of_cachedAction 647 [5] 7 1
    (by decide) (by decide) (by decide) 137
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0648 : HasPrimeObstruction (representative 648) := by
  apply obstruction_of_cachedAction 648 [5] 7 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0649 : HasPrimeObstruction (representative 649) := by
  apply obstruction_of_cachedAction 649 [5, 1] 7 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0650 : HasPrimeObstruction (representative 650) := by
  apply obstruction_of_cachedAction 650 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0651 : HasPrimeObstruction (representative 651) := by
  apply obstruction_of_cachedAction 651 [5] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0652 : HasPrimeObstruction (representative 652) := by
  apply obstruction_of_cachedAction 652 [5, 3] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0653 : HasPrimeObstruction (representative 653) := by
  apply obstruction_of_cachedAction 653 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0654 : HasPrimeObstruction (representative 654) := by
  apply obstruction_of_cachedAction 654 [5] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0655 : HasPrimeObstruction (representative 655) := by
  apply obstruction_of_cachedAction 655 [5] 5 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0656 : HasPrimeObstruction (representative 656) := by
  apply obstruction_of_cachedAction 656 [5, 3] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0657 : HasPrimeObstruction (representative 657) := by
  apply obstruction_of_cachedAction 657 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0658 : HasPrimeObstruction (representative 658) := by
  apply obstruction_of_cachedAction 658 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0659 : HasPrimeObstruction (representative 659) := by
  apply obstruction_of_cachedAction 659 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0660 : HasPrimeObstruction (representative 660) := by
  apply obstruction_of_cachedAction 660 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0661 : HasPrimeObstruction (representative 661) := by
  apply obstruction_of_cachedAction 661 [5] 5 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0662 : HasPrimeObstruction (representative 662) := by
  apply obstruction_of_cachedAction 662 [5] 7 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0663 : HasPrimeObstruction (representative 663) := by
  apply obstruction_of_cachedAction 663 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0664 : HasPrimeObstruction (representative 664) := by
  apply obstruction_of_cachedAction 664 [5, 2] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0665 : HasPrimeObstruction (representative 665) := by
  apply obstruction_of_cachedAction 665 [5, 1] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0666 : HasPrimeObstruction (representative 666) := by
  apply obstruction_of_cachedAction 666 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0667 : HasPrimeObstruction (representative 667) := by
  apply obstruction_of_cachedAction 667 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0668 : HasPrimeObstruction (representative 668) := by
  apply obstruction_of_cachedAction 668 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0669 : HasPrimeObstruction (representative 669) := by
  apply obstruction_of_cachedAction 669 [5, 1] 7 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0670 : HasPrimeObstruction (representative 670) := by
  apply obstruction_of_cachedAction 670 [5] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0671 : HasPrimeObstruction (representative 671) := by
  apply obstruction_of_cachedAction 671 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0672 : HasPrimeObstruction (representative 672) := by
  apply obstruction_of_cachedAction 672 [5] 7 1
    (by decide) (by decide) (by decide) 111
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0673 : HasPrimeObstruction (representative 673) := by
  apply obstruction_of_cachedAction 673 [5, 2] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0674 : HasPrimeObstruction (representative 674) := by
  apply obstruction_of_cachedAction 674 [5, 2] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0675 : HasPrimeObstruction (representative 675) := by
  apply obstruction_of_cachedAction 675 [5] 7 1
    (by decide) (by decide) (by decide) 98
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0676 : HasPrimeObstruction (representative 676) := by
  apply obstruction_of_cachedAction 676 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0677 : HasPrimeObstruction (representative 677) := by
  apply obstruction_of_cachedAction 677 [5, 1] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0678 : HasPrimeObstruction (representative 678) := by
  apply obstruction_of_cachedAction 678 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0679 : HasPrimeObstruction (representative 679) := by
  apply obstruction_of_cachedAction 679 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0680 : HasPrimeObstruction (representative 680) := by
  apply obstruction_of_cachedAction 680 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0681 : HasPrimeObstruction (representative 681) := by
  apply obstruction_of_cachedAction 681 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0682 : HasPrimeObstruction (representative 682) := by
  apply obstruction_of_cachedAction 682 [5] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0683 : HasPrimeObstruction (representative 683) := by
  apply obstruction_of_cachedAction 683 [5] 7 1
    (by decide) (by decide) (by decide) 98
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0684 : HasPrimeObstruction (representative 684) := by
  apply obstruction_of_cachedAction 684 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0685 : HasPrimeObstruction (representative 685) := by
  apply obstruction_of_cachedAction 685 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0686 : HasPrimeObstruction (representative 686) := by
  apply obstruction_of_cachedAction 686 [5, 1] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0687 : HasPrimeObstruction (representative 687) := by
  apply obstruction_of_cachedAction 687 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0688 : HasPrimeObstruction (representative 688) := by
  apply obstruction_of_cachedAction 688 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0689 : HasPrimeObstruction (representative 689) := by
  apply obstruction_of_cachedAction 689 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0690 : HasPrimeObstruction (representative 690) := by
  apply obstruction_of_cachedAction 690 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0691 : HasPrimeObstruction (representative 691) := by
  apply obstruction_of_cachedAction 691 [5] 7 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0692 : HasPrimeObstruction (representative 692) := by
  apply obstruction_of_cachedAction 692 [5, 2] 7 1
    (by decide) (by decide) (by decide) 34
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0693 : HasPrimeObstruction (representative 693) := by
  apply obstruction_of_cachedAction 693 [5] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0694 : HasPrimeObstruction (representative 694) := by
  apply obstruction_of_cachedAction 694 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0695 : HasPrimeObstruction (representative 695) := by
  apply obstruction_of_cachedAction 695 [5] 7 1
    (by decide) (by decide) (by decide) 57
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0696 : HasPrimeObstruction (representative 696) := by
  apply obstruction_of_cachedAction 696 [5, 4] 5 1
    (by decide) (by decide) (by decide) 82
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0697 : HasPrimeObstruction (representative 697) := by
  apply obstruction_of_cachedAction 697 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0698 : HasPrimeObstruction (representative 698) := by
  apply obstruction_of_cachedAction 698 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0699 : HasPrimeObstruction (representative 699) := by
  apply obstruction_of_cachedAction 699 [5, 2] 5 1
    (by decide) (by decide) (by decide) 149
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0700 : HasPrimeObstruction (representative 700) := by
  apply obstruction_of_cachedAction 700 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0701 : HasPrimeObstruction (representative 701) := by
  apply obstruction_of_cachedAction 701 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0702 : HasPrimeObstruction (representative 702) := by
  apply obstruction_of_cachedAction 702 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0703 : HasPrimeObstruction (representative 703) := by
  apply obstruction_of_cachedAction 703 [5] 5 1
    (by decide) (by decide) (by decide) 97
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0704 : HasPrimeObstruction (representative 704) := by
  apply obstruction_of_cachedAction 704 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0705 : HasPrimeObstruction (representative 705) := by
  apply obstruction_of_cachedAction 705 [5, 2] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0706 : HasPrimeObstruction (representative 706) := by
  apply obstruction_of_cachedAction 706 [5, 3] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0707 : HasPrimeObstruction (representative 707) := by
  apply obstruction_of_cachedAction 707 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0708 : HasPrimeObstruction (representative 708) := by
  apply obstruction_of_cachedAction 708 [5] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0709 : HasPrimeObstruction (representative 709) := by
  apply obstruction_of_cachedAction 709 [5] 7 1
    (by decide) (by decide) (by decide) 294
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0710 : HasPrimeObstruction (representative 710) := by
  apply obstruction_of_cachedAction 710 [5] 7 1
    (by decide) (by decide) (by decide) 200
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0711 : HasPrimeObstruction (representative 711) := by
  apply obstruction_of_cachedAction 711 [5] 7 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0712 : HasPrimeObstruction (representative 712) := by
  apply obstruction_of_cachedAction 712 [5] 5 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0713 : HasPrimeObstruction (representative 713) := by
  apply obstruction_of_cachedAction 713 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0714 : HasPrimeObstruction (representative 714) := by
  apply obstruction_of_cachedAction 714 [5] 7 1
    (by decide) (by decide) (by decide) 40
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0715 : HasPrimeObstruction (representative 715) := by
  apply obstruction_of_cachedAction 715 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0716 : HasPrimeObstruction (representative 716) := by
  apply obstruction_of_cachedAction 716 [5, 1] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0717 : HasPrimeObstruction (representative 717) := by
  apply obstruction_of_cachedAction 717 [5, 4] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0718 : HasPrimeObstruction (representative 718) := by
  apply obstruction_of_cachedAction 718 [5] 7 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0719 : HasPrimeObstruction (representative 719) := by
  apply obstruction_of_cachedAction 719 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0720 : HasPrimeObstruction (representative 720) := by
  apply obstruction_of_cachedAction 720 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0721 : HasPrimeObstruction (representative 721) := by
  apply obstruction_of_cachedAction 721 [5, 2] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0722 : HasPrimeObstruction (representative 722) := by
  apply obstruction_of_cachedAction 722 [5, 1] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0723 : HasPrimeObstruction (representative 723) := by
  apply obstruction_of_cachedAction 723 [5, 1] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0724 : HasPrimeObstruction (representative 724) := by
  apply obstruction_of_cachedAction 724 [5, 2] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0725 : HasPrimeObstruction (representative 725) := by
  apply obstruction_of_cachedAction 725 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0726 : HasPrimeObstruction (representative 726) := by
  apply obstruction_of_cachedAction 726 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0727 : HasPrimeObstruction (representative 727) := by
  apply obstruction_of_cachedAction 727 [5, 2] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0728 : HasPrimeObstruction (representative 728) := by
  apply obstruction_of_cachedAction 728 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0729 : HasPrimeObstruction (representative 729) := by
  apply obstruction_of_cachedAction 729 [5, 1] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0730 : HasPrimeObstruction (representative 730) := by
  apply obstruction_of_cachedAction 730 [5] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0731 : HasPrimeObstruction (representative 731) := by
  apply obstruction_of_cachedAction 731 [5] 7 1
    (by decide) (by decide) (by decide) 119
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0732 : HasPrimeObstruction (representative 732) := by
  apply obstruction_of_cachedAction 732 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0733 : HasPrimeObstruction (representative 733) := by
  apply obstruction_of_cachedAction 733 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0734 : HasPrimeObstruction (representative 734) := by
  apply obstruction_of_cachedAction 734 [5, 2] 5 1
    (by decide) (by decide) (by decide) 97
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0735 : HasPrimeObstruction (representative 735) := by
  apply obstruction_of_cachedAction 735 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0736 : HasPrimeObstruction (representative 736) := by
  apply obstruction_of_cachedAction 736 [5] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0737 : HasPrimeObstruction (representative 737) := by
  apply obstruction_of_cachedAction 737 [5] 7 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0738 : HasPrimeObstruction (representative 738) := by
  apply obstruction_of_cachedAction 738 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0739 : HasPrimeObstruction (representative 739) := by
  apply obstruction_of_cachedAction 739 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0740 : HasPrimeObstruction (representative 740) := by
  apply obstruction_of_cachedAction 740 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0741 : HasPrimeObstruction (representative 741) := by
  apply obstruction_of_cachedAction 741 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0742 : HasPrimeObstruction (representative 742) := by
  apply obstruction_of_cachedAction 742 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0743 : HasPrimeObstruction (representative 743) := by
  apply obstruction_of_cachedAction 743 [5, 1] 5 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0744 : HasPrimeObstruction (representative 744) := by
  apply obstruction_of_cachedAction 744 [5] 7 1
    (by decide) (by decide) (by decide) 107
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0745 : HasPrimeObstruction (representative 745) := by
  apply obstruction_of_cachedAction 745 [5] 5 1
    (by decide) (by decide) (by decide) 63
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0746 : HasPrimeObstruction (representative 746) := by
  apply obstruction_of_cachedAction 746 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0747 : HasPrimeObstruction (representative 747) := by
  apply obstruction_of_cachedAction 747 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0748 : HasPrimeObstruction (representative 748) := by
  apply obstruction_of_cachedAction 748 [5, 2] 7 1
    (by decide) (by decide) (by decide) 368
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0749 : HasPrimeObstruction (representative 749) := by
  apply obstruction_of_cachedAction 749 [5] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0750 : HasPrimeObstruction (representative 750) := by
  apply obstruction_of_cachedAction 750 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0751 : HasPrimeObstruction (representative 751) := by
  apply obstruction_of_cachedAction 751 [5, 1] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0752 : HasPrimeObstruction (representative 752) := by
  apply obstruction_of_cachedAction 752 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0753 : HasPrimeObstruction (representative 753) := by
  apply obstruction_of_cachedAction 753 [5, 2] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0754 : HasPrimeObstruction (representative 754) := by
  apply obstruction_of_cachedAction 754 [5, 2] 7 1
    (by decide) (by decide) (by decide) 83
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0755 : HasPrimeObstruction (representative 755) := by
  apply obstruction_of_cachedAction 755 [5, 4] 5 1
    (by decide) (by decide) (by decide) 67
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0756 : HasPrimeObstruction (representative 756) := by
  apply obstruction_of_cachedAction 756 [5, 3] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0757 : HasPrimeObstruction (representative 757) := by
  apply obstruction_of_cachedAction 757 [5, 3] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0758 : HasPrimeObstruction (representative 758) := by
  apply obstruction_of_cachedAction 758 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0759 : HasPrimeObstruction (representative 759) := by
  apply obstruction_of_cachedAction 759 [5] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0760 : HasPrimeObstruction (representative 760) := by
  apply obstruction_of_cachedAction 760 [5] 7 1
    (by decide) (by decide) (by decide) 113
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0761 : HasPrimeObstruction (representative 761) := by
  apply obstruction_of_cachedAction 761 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0762 : HasPrimeObstruction (representative 762) := by
  apply obstruction_of_cachedAction 762 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0763 : HasPrimeObstruction (representative 763) := by
  apply obstruction_of_cachedAction 763 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0764 : HasPrimeObstruction (representative 764) := by
  apply obstruction_of_cachedAction 764 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0765 : HasPrimeObstruction (representative 765) := by
  apply obstruction_of_cachedAction 765 [5] 7 1
    (by decide) (by decide) (by decide) 54
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0766 : HasPrimeObstruction (representative 766) := by
  apply obstruction_of_cachedAction 766 [5] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0767 : HasPrimeObstruction (representative 767) := by
  apply obstruction_of_cachedAction 767 [5] 7 1
    (by decide) (by decide) (by decide) 215
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block02 (j : Fin 256)
    (h : localBranch ⟨512 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨512 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_0512
  · exact obstruction_0513
  · exact obstruction_0514
  · exact obstruction_0515
  · exact obstruction_0516
  · exact obstruction_0517
  · exact obstruction_0518
  · exact obstruction_0519
  · exact obstruction_0520
  · exact obstruction_0521
  · exact obstruction_0522
  · exact obstruction_0523
  · exact obstruction_0524
  · exact obstruction_0525
  · exact obstruction_0526
  · exact obstruction_0527
  · exact obstruction_0528
  · exact obstruction_0529
  · exact obstruction_0530
  · exact obstruction_0531
  · exact obstruction_0532
  · exact obstruction_0533
  · exact obstruction_0534
  · exact obstruction_0535
  · exact obstruction_0536
  · exact obstruction_0537
  · exact obstruction_0538
  · exact obstruction_0539
  · exact obstruction_0540
  · exact obstruction_0541
  · exact obstruction_0542
  · exact obstruction_0543
  · exact obstruction_0544
  · exact obstruction_0545
  · exact obstruction_0546
  · exact obstruction_0547
  · exact obstruction_0548
  · exact obstruction_0549
  · exact obstruction_0550
  · exact obstruction_0551
  · exact obstruction_0552
  · exact obstruction_0553
  · exact obstruction_0554
  · exact obstruction_0555
  · exact obstruction_0556
  · exact obstruction_0557
  · exact obstruction_0558
  · exact obstruction_0559
  · exact obstruction_0560
  · exact obstruction_0561
  · exact obstruction_0562
  · exact obstruction_0563
  · exact obstruction_0564
  · exact obstruction_0565
  · exact obstruction_0566
  · exact obstruction_0567
  · exact obstruction_0568
  · exact obstruction_0569
  · exact obstruction_0570
  · exact obstruction_0571
  · exact obstruction_0572
  · exact obstruction_0573
  · exact obstruction_0574
  · exact obstruction_0575
  · exact obstruction_0576
  · exact obstruction_0577
  · exact obstruction_0578
  · exact obstruction_0579
  · exact obstruction_0580
  · exact obstruction_0581
  · exact obstruction_0582
  · exact obstruction_0583
  · exact obstruction_0584
  · exact obstruction_0585
  · exact obstruction_0586
  · exact obstruction_0587
  · exact obstruction_0588
  · exact obstruction_0589
  · exact obstruction_0590
  · exact obstruction_0591
  · exact obstruction_0592
  · exact obstruction_0593
  · exact obstruction_0594
  · exact obstruction_0595
  · exact obstruction_0596
  · exact obstruction_0597
  · exact obstruction_0598
  · exact obstruction_0599
  · exact obstruction_0600
  · exact obstruction_0601
  · exact obstruction_0602
  · exact obstruction_0603
  · exact obstruction_0604
  · exact obstruction_0605
  · exact obstruction_0606
  · exact obstruction_0607
  · exact obstruction_0608
  · exact obstruction_0609
  · exact obstruction_0610
  · exact obstruction_0611
  · exact obstruction_0612
  · exact obstruction_0613
  · exact obstruction_0614
  · exact obstruction_0615
  · exact obstruction_0616
  · exact obstruction_0617
  · exact obstruction_0618
  · exact obstruction_0619
  · exact obstruction_0620
  · exact obstruction_0621
  · exact obstruction_0622
  · exact obstruction_0623
  · exact obstruction_0624
  · exact obstruction_0625
  · exact obstruction_0626
  · exact obstruction_0627
  · exact obstruction_0628
  · exact obstruction_0629
  · exact obstruction_0630
  · exact obstruction_0631
  · exact obstruction_0632
  · exact obstruction_0633
  · exact obstruction_0634
  · exact obstruction_0635
  · exact obstruction_0636
  · exact obstruction_0637
  · exact obstruction_0638
  · exact obstruction_0639
  · exact obstruction_0640
  · exact obstruction_0641
  · exact obstruction_0642
  · exact obstruction_0643
  · exact obstruction_0644
  · exact obstruction_0645
  · exact obstruction_0646
  · exact obstruction_0647
  · exact obstruction_0648
  · exact obstruction_0649
  · exact obstruction_0650
  · exact obstruction_0651
  · exact obstruction_0652
  · exact obstruction_0653
  · exact obstruction_0654
  · exact obstruction_0655
  · exact obstruction_0656
  · exact obstruction_0657
  · exact obstruction_0658
  · exact obstruction_0659
  · exact obstruction_0660
  · exact obstruction_0661
  · exact obstruction_0662
  · exact obstruction_0663
  · exact obstruction_0664
  · exact obstruction_0665
  · exact obstruction_0666
  · exact obstruction_0667
  · exact obstruction_0668
  · exact obstruction_0669
  · exact obstruction_0670
  · exact obstruction_0671
  · exact obstruction_0672
  · exact obstruction_0673
  · exact obstruction_0674
  · exact obstruction_0675
  · exact obstruction_0676
  · exact obstruction_0677
  · exact obstruction_0678
  · exact obstruction_0679
  · exact obstruction_0680
  · exact obstruction_0681
  · exact obstruction_0682
  · exact obstruction_0683
  · exact obstruction_0684
  · exact obstruction_0685
  · exact obstruction_0686
  · exact obstruction_0687
  · exact obstruction_0688
  · exact obstruction_0689
  · exact obstruction_0690
  · exact obstruction_0691
  · exact obstruction_0692
  · exact obstruction_0693
  · exact obstruction_0694
  · exact obstruction_0695
  · exact obstruction_0696
  · exact obstruction_0697
  · exact obstruction_0698
  · exact obstruction_0699
  · exact obstruction_0700
  · exact obstruction_0701
  · exact obstruction_0702
  · exact obstruction_0703
  · exact obstruction_0704
  · exact obstruction_0705
  · exact obstruction_0706
  · exact obstruction_0707
  · exact obstruction_0708
  · exact obstruction_0709
  · exact obstruction_0710
  · exact obstruction_0711
  · exact obstruction_0712
  · exact obstruction_0713
  · exact obstruction_0714
  · exact obstruction_0715
  · exact obstruction_0716
  · exact obstruction_0717
  · exact obstruction_0718
  · exact obstruction_0719
  · exact obstruction_0720
  · exact obstruction_0721
  · exact obstruction_0722
  · exact obstruction_0723
  · exact obstruction_0724
  · exact obstruction_0725
  · exact obstruction_0726
  · exact obstruction_0727
  · exact obstruction_0728
  · exact obstruction_0729
  · exact obstruction_0730
  · exact obstruction_0731
  · exact obstruction_0732
  · exact obstruction_0733
  · exact obstruction_0734
  · exact obstruction_0735
  · exact obstruction_0736
  · exact obstruction_0737
  · exact obstruction_0738
  · exact obstruction_0739
  · exact obstruction_0740
  · exact obstruction_0741
  · exact obstruction_0742
  · exact obstruction_0743
  · exact obstruction_0744
  · exact obstruction_0745
  · exact obstruction_0746
  · exact obstruction_0747
  · exact obstruction_0748
  · exact obstruction_0749
  · exact obstruction_0750
  · exact obstruction_0751
  · exact obstruction_0752
  · exact obstruction_0753
  · exact obstruction_0754
  · exact obstruction_0755
  · exact obstruction_0756
  · exact obstruction_0757
  · exact obstruction_0758
  · exact obstruction_0759
  · exact obstruction_0760
  · exact obstruction_0761
  · exact obstruction_0762
  · exact obstruction_0763
  · exact obstruction_0764
  · exact obstruction_0765
  · exact obstruction_0766
  · exact obstruction_0767

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
