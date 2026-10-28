module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB400
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB410
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB420
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB430
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB440
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB450
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB460
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB470
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB480
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalClassificationUpperB490

/-!
# Maximal-subgroup classification for small even nodes 400–499

The ten certificate modules check the generating words and every binary
Schreier branch against the group arithmetic. Finite case analysis applies
their soundness theorems without changing the node or edge numbering.

Source: Shinoda (1975), (2.3), pp. 81–82; the root-word conventions and
input provenance are recorded in `SmallEvenDescentEdgeData`.
-/

namespace ReeTwo.SylowModel.SmallEvenUpperCertificates

/-- Every maximal subgroup of nodes 400–499 lies in the core, has an outside
centralizer witness, or equals one of the recorded edges. -/
public theorem classified400To499 (i : Fin 600) (hlo : 400 ≤ i.val)
    (hhi : i.val < 500) (H : Subgroup SylowModel)
    (h : H ⋖ smallEvenDescentNode i) : Classified H := by
  rcases i with ⟨i, hi⟩
  change 400 ≤ i at hlo
  change i < 500 at hhi
  interval_cases i
  · exact classified400 H h
  · exact classified401 H h
  · exact classified402 H h
  · exact classified403 H h
  · exact classified404 H h
  · exact classified405 H h
  · exact classified406 H h
  · exact classified407 H h
  · exact classified408 H h
  · exact classified409 H h
  · exact classified410 H h
  · exact classified411 H h
  · exact classified412 H h
  · exact classified413 H h
  · exact classified414 H h
  · exact classified415 H h
  · exact classified416 H h
  · exact classified417 H h
  · exact classified418 H h
  · exact classified419 H h
  · exact classified420 H h
  · exact classified421 H h
  · exact classified422 H h
  · exact classified423 H h
  · exact classified424 H h
  · exact classified425 H h
  · exact classified426 H h
  · exact classified427 H h
  · exact classified428 H h
  · exact classified429 H h
  · exact classified430 H h
  · exact classified431 H h
  · exact classified432 H h
  · exact classified433 H h
  · exact classified434 H h
  · exact classified435 H h
  · exact classified436 H h
  · exact classified437 H h
  · exact classified438 H h
  · exact classified439 H h
  · exact classified440 H h
  · exact classified441 H h
  · exact classified442 H h
  · exact classified443 H h
  · exact classified444 H h
  · exact classified445 H h
  · exact classified446 H h
  · exact classified447 H h
  · exact classified448 H h
  · exact classified449 H h
  · exact classified450 H h
  · exact classified451 H h
  · exact classified452 H h
  · exact classified453 H h
  · exact classified454 H h
  · exact classified455 H h
  · exact classified456 H h
  · exact classified457 H h
  · exact classified458 H h
  · exact classified459 H h
  · exact classified460 H h
  · exact classified461 H h
  · exact classified462 H h
  · exact classified463 H h
  · exact classified464 H h
  · exact classified465 H h
  · exact classified466 H h
  · exact classified467 H h
  · exact classified468 H h
  · exact classified469 H h
  · exact classified470 H h
  · exact classified471 H h
  · exact classified472 H h
  · exact classified473 H h
  · exact classified474 H h
  · exact classified475 H h
  · exact classified476 H h
  · exact classified477 H h
  · exact classified478 H h
  · exact classified479 H h
  · exact classified480 H h
  · exact classified481 H h
  · exact classified482 H h
  · exact classified483 H h
  · exact classified484 H h
  · exact classified485 H h
  · exact classified486 H h
  · exact classified487 H h
  · exact classified488 H h
  · exact classified489 H h
  · exact classified490 H h
  · exact classified491 H h
  · exact classified492 H h
  · exact classified493 H h
  · exact classified494 H h
  · exact classified495 H h
  · exact classified496 H h
  · exact classified497 H h
  · exact classified498 H h
  · exact classified499 H h

end ReeTwo.SylowModel.SmallEvenUpperCertificates
