module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked05

/-!
# Checked Tietze relations (block 6)

Every input is read from the literal point Schreier presentation. Explicit
intermediate words prevent recursive reconstruction of the discovery trace.
See `../source/README.md` for the deterministic, untrusted producer.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G] (g : Nat → G)
  (hi : ∀ r, eval g (inputWord r) = 1)
include hi

theorem h515 : eval g w515 = 1 := by
  exact rewrite_relation g w514 w34 w515 false 0 3 false 20
    (by decide +kernel) (h514 g hi) (h34 g hi)

theorem h516 : eval g w516 = 1 := by
  exact rewrite_relation g w515 w34 w516 false 0 3 true 35
    (by decide +kernel) (h515 g hi) (h34 g hi)

theorem h517 : eval g w517 = 1 := by
  exact rewrite_relation g w516 w496 w517 false 9 0 true 169
    (by decide +kernel) (h516 g hi) (h496 g hi)

theorem h518 : eval g w518 = 1 := by
  exact rewrite_relation g w511 w487 w518 false 114 3 false 187
    (by decide +kernel) (h511 g hi) (h487 g hi)

theorem h519 : eval g w519 = 1 := by
  exact rewrite_relation g w517 w34 w519 false 0 3 false 20
    (by decide +kernel) (h517 g hi) (h34 g hi)

theorem h520 : eval g w520 = 1 := by
  exact rewrite_relation g w519 w34 w520 false 0 3 false 22
    (by decide +kernel) (h519 g hi) (h34 g hi)

theorem h521 : eval g w521 = 1 := by
  exact rewrite_relation g w520 w34 w521 false 0 5 false 34
    (by decide +kernel) (h520 g hi) (h34 g hi)

theorem h522 : eval g w522 = 1 := by
  exact rewrite_relation g w521 w34 w522 false 0 5 false 34
    (by decide +kernel) (h521 g hi) (h34 g hi)

theorem h523 : eval g w523 = 1 := by
  exact rewrite_relation g w522 w34 w523 false 0 5 false 34
    (by decide +kernel) (h522 g hi) (h34 g hi)

theorem h524 : eval g w524 = 1 := by
  exact rewrite_relation g w523 w34 w524 false 0 5 false 34
    (by decide +kernel) (h523 g hi) (h34 g hi)

theorem h525 : eval g w525 = 1 := by
  exact rewrite_relation g w524 w34 w525 false 0 5 false 34
    (by decide +kernel) (h524 g hi) (h34 g hi)

theorem h526 : eval g w526 = 1 := by
  exact rewrite_relation g w525 w34 w526 false 0 21 false 17
    (by decide +kernel) (h525 g hi) (h34 g hi)

theorem h527 : eval g w527 = 1 := by
  exact rewrite_relation g w526 w34 w527 false 0 21 false 17
    (by decide +kernel) (h526 g hi) (h34 g hi)

theorem h528 : eval g w528 = 1 := by
  exact rewrite_relation g w527 w34 w528 false 0 21 false 17
    (by decide +kernel) (h527 g hi) (h34 g hi)

theorem h529 : eval g w529 = 1 := by
  exact rewrite_relation g w528 w34 w529 false 0 21 false 17
    (by decide +kernel) (h528 g hi) (h34 g hi)

theorem h530 : eval g w530 = 1 := by
  exact rewrite_relation g w529 w34 w530 false 0 21 false 17
    (by decide +kernel) (h529 g hi) (h34 g hi)

theorem h531 : eval g w531 = 1 := by
  exact rewrite_relation g w518 w34 w531 true 0 18 false 171
    (by decide +kernel) (h518 g hi) (h34 g hi)

theorem h532 : eval g w532 = 1 := by
  exact rewrite_relation g w531 w497 w532 false 4 34 false 137
    (by decide +kernel) (h531 g hi) (h497 g hi)

theorem h533 : eval g w533 = 1 := by
  exact rewrite_relation g w502 w34 w533 false 0 3 false 86
    (by decide +kernel) (h502 g hi) (h34 g hi)

theorem h534 : eval g w534 = 1 := by
  exact rewrite_relation g w533 w34 w534 false 0 3 false 32
    (by decide +kernel) (h533 g hi) (h34 g hi)

theorem h535 : eval g w535 = 1 := by
  exact rewrite_relation g w534 w34 w535 true 0 31 false 146
    (by decide +kernel) (h534 g hi) (h34 g hi)

theorem h536 : eval g w536 = 1 := by
  exact rewrite_relation g w535 w34 w536 false 0 35 false 141
    (by decide +kernel) (h535 g hi) (h34 g hi)

theorem h537 : eval g w537 = 1 := by
  exact rewrite_relation g w536 w489 w537 true 12 56 false 12
    (by decide +kernel) (h536 g hi) (h489 g hi)

theorem h538 : eval g w538 = 1 := by
  exact rewrite_relation g w532 w489 w538 true 12 34 false 92
    (by decide +kernel) (h532 g hi) (h489 g hi)

theorem h539 : eval g w539 = 1 := by
  exact rewrite_relation g w488 w497 w539 false 1 4 true 134
    (by decide +kernel) (h488 g hi) (h497 g hi)

theorem h540 : eval g w540 = 1 := by
  exact rewrite_relation g w491 w496 w540 false 9 0 true 111
    (by decide +kernel) (h491 g hi) (h496 g hi)

theorem h541 : eval g w541 = 1 := by
  exact rewrite_relation g w539 w496 w541 false 5 8 true 115
    (by decide +kernel) (h539 g hi) (h496 g hi)

theorem h542 : eval g w542 = 1 := by
  exact rewrite_relation g w537 w34 w542 false 0 6 false 120
    (by decide +kernel) (h537 g hi) (h34 g hi)

theorem h543 : eval g w543 = 1 := by
  exact rewrite_relation g w538 w487 w543 false 114 49 false 50
    (by decide +kernel) (h538 g hi) (h487 g hi)

theorem h544 : eval g w544 = 1 := by
  exact rewrite_relation g w542 w489 w544 true 12 27 false 12
    (by decide +kernel) (h542 g hi) (h489 g hi)

theorem h545 : eval g w545 = 1 := by
  exact rewrite_relation g w541 w34 w545 false 0 3 true 43
    (by decide +kernel) (h541 g hi) (h34 g hi)

theorem h546 : eval g w546 = 1 := by
  exact rewrite_relation g w540 w34 w546 false 0 3 false 88
    (by decide +kernel) (h540 g hi) (h34 g hi)

theorem h547 : eval g w547 = 1 := by
  exact rewrite_relation g w487 w34 w547 false 0 3 true 38
    (by decide +kernel) (h487 g hi) (h34 g hi)

theorem h548 : eval g w548 = 1 := by
  exact rewrite_relation g w545 w496 w548 false 9 0 true 57
    (by decide +kernel) (h545 g hi) (h496 g hi)

theorem h549 : eval g w549 = 1 := by
  exact rewrite_relation g w546 w34 w549 false 0 3 false 29
    (by decide +kernel) (h546 g hi) (h34 g hi)

theorem h550 : eval g w550 = 1 := by
  exact rewrite_relation g w547 w497 w550 false 0 0 true 102
    (by decide +kernel) (h547 g hi) (h497 g hi)

theorem h551 : eval g w551 = 1 := by
  exact rewrite_relation g w549 w496 w551 false 9 0 true 80
    (by decide +kernel) (h549 g hi) (h496 g hi)

theorem h552 : eval g w552 = 1 := by
  exact rewrite_relation g w550 w34 w552 false 0 19 false 84
    (by decide +kernel) (h550 g hi) (h34 g hi)

theorem h553 : eval g w553 = 1 := by
  exact rewrite_relation g w552 w496 w553 false 13 40 false 46
    (by decide +kernel) (h552 g hi) (h496 g hi)

theorem h554 : eval g w554 = 1 := by
  exact rewrite_relation g w486 w34 w554 true 0 16 false 85
    (by decide +kernel) (h486 g hi) (h34 g hi)

theorem h555 : eval g w555 = 1 := by
  exact rewrite_relation g w499 w34 w555 false 0 3 false 45
    (by decide +kernel) (h499 g hi) (h34 g hi)

theorem h556 : eval g w556 = 1 := by
  exact rewrite_relation g w554 w34 w556 true 0 18 false 82
    (by decide +kernel) (h554 g hi) (h34 g hi)

theorem h557 : eval g w557 = 1 := by
  exact rewrite_relation g w492 w497 w557 false 0 0 true 88
    (by decide +kernel) (h492 g hi) (h497 g hi)

theorem h558 : eval g w558 = 1 := by
  exact rewrite_relation g w503 w34 w558 false 0 10 false 9
    (by decide +kernel) (h503 g hi) (h34 g hi)

theorem h559 : eval g w559 = 1 := by
  exact rewrite_relation g w556 w496 w559 false 13 29 false 54
    (by decide +kernel) (h556 g hi) (h496 g hi)

theorem h560 : eval g w560 = 1 := by
  exact rewrite_relation g w543 w34 w560 true 0 64 false 34
    (by decide +kernel) (h543 g hi) (h34 g hi)

theorem h561 : eval g w561 = 1 := by
  exact rewrite_relation g w558 w34 w561 false 0 10 false 9
    (by decide +kernel) (h558 g hi) (h34 g hi)

theorem h562 : eval g w562 = 1 := by
  exact rewrite_relation g w560 w497 w562 false 4 80 false 12
    (by decide +kernel) (h560 g hi) (h497 g hi)

theorem h563 : eval g w563 = 1 := by
  exact rewrite_relation g w561 w34 w563 false 0 10 false 9
    (by decide +kernel) (h561 g hi) (h34 g hi)

theorem h564 : eval g w564 = 1 := by
  exact rewrite_relation g w555 w34 w564 false 0 3 false 2
    (by decide +kernel) (h555 g hi) (h34 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
