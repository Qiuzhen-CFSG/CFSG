module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked06

/-!
# Checked Tietze relations (block 7)

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

theorem h565 : eval g w565 = 1 := by
  exact rewrite_relation g w563 w34 w565 false 0 10 false 9
    (by decide +kernel) (h563 g hi) (h34 g hi)

theorem h566 : eval g w566 = 1 := by
  exact rewrite_relation g w565 w34 w566 false 0 10 false 9
    (by decide +kernel) (h565 g hi) (h34 g hi)

theorem h567 : eval g w567 = 1 := by
  exact rewrite_relation g w493 w496 w567 false 6 6 false 55
    (by decide +kernel) (h493 g hi) (h496 g hi)

theorem h568 : eval g w568 = 1 := by
  exact rewrite_relation g w564 w489 w568 true 8 0 false 84
    (by decide +kernel) (h564 g hi) (h489 g hi)

theorem h569 : eval g w569 = 1 := by
  exact rewrite_relation g w557 w497 w569 false 3 14 true 75
    (by decide +kernel) (h557 g hi) (h497 g hi)

theorem h570 : eval g w570 = 1 := by
  exact rewrite_relation g w544 w34 w570 false 0 9 false 36
    (by decide +kernel) (h544 g hi) (h34 g hi)

theorem h571 : eval g w571 = 1 := by
  exact rewrite_relation g w553 w34 w571 true 0 39 false 46
    (by decide +kernel) (h553 g hi) (h34 g hi)

theorem h572 : eval g w572 = 1 := by
  exact rewrite_relation g w489 w496 w572 false 8 3 false 55
    (by decide +kernel) (h489 g hi) (h496 g hi)

theorem h573 : eval g w573 = 1 := by
  exact rewrite_relation g w551 w34 w573 false 0 3 false 57
    (by decide +kernel) (h551 g hi) (h34 g hi)

theorem h574 : eval g w574 = 1 := by
  exact rewrite_relation g w568 w34 w574 false 0 18 false 66
    (by decide +kernel) (h568 g hi) (h34 g hi)

theorem h575 : eval g w575 = 1 := by
  exact rewrite_relation g w571 w501 w575 true 16 36 false 43
    (by decide +kernel) (h571 g hi) (h501 g hi)

theorem h576 : eval g w576 = 1 := by
  exact rewrite_relation g w573 w34 w576 false 0 3 true 35
    (by decide +kernel) (h573 g hi) (h34 g hi)

theorem h577 : eval g w577 = 1 := by
  exact rewrite_relation g w574 w34 w577 false 0 46 false 37
    (by decide +kernel) (h574 g hi) (h34 g hi)

theorem h578 : eval g w578 = 1 := by
  exact rewrite_relation g w496 w34 w578 false 0 3 false 5
    (by decide +kernel) (h496 g hi) (h34 g hi)

theorem h579 : eval g w579 = 1 := by
  exact rewrite_relation g w559 w572 w579 false 22 29 true 53
    (by decide +kernel) (h559 g hi) (h572 g hi)

theorem h580 : eval g w580 = 1 := by
  exact rewrite_relation g w576 w34 w580 false 0 5 true 45
    (by decide +kernel) (h576 g hi) (h34 g hi)

theorem h581 : eval g w581 = 1 := by
  exact rewrite_relation g w577 w34 w581 false 0 65 false 17
    (by decide +kernel) (h577 g hi) (h34 g hi)

theorem h582 : eval g w582 = 1 := by
  exact rewrite_relation g w578 w34 w582 false 0 5 false 53
    (by decide +kernel) (h578 g hi) (h34 g hi)

theorem h583 : eval g w583 = 1 := by
  exact rewrite_relation g w580 w34 w583 false 0 5 false 53
    (by decide +kernel) (h580 g hi) (h34 g hi)

theorem h584 : eval g w584 = 1 := by
  exact rewrite_relation g w582 w34 w584 false 0 5 false 17
    (by decide +kernel) (h582 g hi) (h34 g hi)

theorem h585 : eval g w585 = 1 := by
  exact rewrite_relation g w583 w34 w585 false 0 5 true 22
    (by decide +kernel) (h583 g hi) (h34 g hi)

theorem h586 : eval g w586 = 1 := by
  exact rewrite_relation g w490 w494 w586 true 18 4 false 65
    (by decide +kernel) (h490 g hi) (h494 g hi)

theorem h587 : eval g w587 = 1 := by
  exact rewrite_relation g w548 w34 w587 false 0 3 false 5
    (by decide +kernel) (h548 g hi) (h34 g hi)

theorem h588 : eval g w588 = 1 := by
  exact rewrite_relation g w584 w569 w588 false 18 6 true 46
    (by decide +kernel) (h584 g hi) (h569 g hi)

theorem h589 : eval g w589 = 1 := by
  exact rewrite_relation g w575 w34 w589 false 0 35 false 43
    (by decide +kernel) (h575 g hi) (h34 g hi)

theorem h590 : eval g w590 = 1 := by
  exact rewrite_relation g w587 w586 w590 false 33 3 true 59
    (by decide +kernel) (h587 g hi) (h586 g hi)

theorem h591 : eval g w591 = 1 := by
  exact rewrite_relation g w569 w34 w591 true 0 57 false 20
    (by decide +kernel) (h569 g hi) (h34 g hi)

theorem h592 : eval g w592 = 1 := by
  exact rewrite_relation g w570 w34 w592 true 0 26 false 51
    (by decide +kernel) (h570 g hi) (h34 g hi)

theorem h593 : eval g w593 = 1 := by
  exact rewrite_relation g w589 w34 w593 false 0 41 false 36
    (by decide +kernel) (h589 g hi) (h34 g hi)

theorem h594 : eval g w594 = 1 := by
  exact rewrite_relation g w592 w34 w594 true 0 64 false 12
    (by decide +kernel) (h592 g hi) (h34 g hi)

theorem h595 : eval g w595 = 1 := by
  exact rewrite_relation g w593 w34 w595 false 0 53 false 23
    (by decide +kernel) (h593 g hi) (h34 g hi)

theorem h596 : eval g w596 = 1 := by
  exact rewrite_relation g w595 w34 w596 true 0 61 false 12
    (by decide +kernel) (h595 g hi) (h34 g hi)

theorem h597 : eval g w597 = 1 := by
  exact rewrite_relation g w562 w596 w597 true 32 3 false 40
    (by decide +kernel) (h562 g hi) (h596 g hi)

theorem h598 : eval g w598 = 1 := by
  exact rewrite_relation g w597 w596 w598 true 32 3 false 1
    (by decide +kernel) (h597 g hi) (h596 g hi)

theorem h599 : eval g w599 = 1 := by
  exact rewrite_relation g w598 w34 w599 false 0 21 false 21
    (by decide +kernel) (h598 g hi) (h34 g hi)

theorem h600 : eval g w600 = 1 := by
  exact rewrite_relation g w599 w34 w600 false 0 21 false 21
    (by decide +kernel) (h599 g hi) (h34 g hi)

theorem h601 : eval g w601 = 1 := by
  exact rewrite_relation g w600 w34 w601 true 0 29 false 54
    (by decide +kernel) (h600 g hi) (h34 g hi)

theorem h602 : eval g w602 = 1 := by
  exact rewrite_relation g w601 w34 w602 true 0 70 false 12
    (by decide +kernel) (h601 g hi) (h34 g hi)

theorem h603 : eval g w603 = 1 := by
  exact rewrite_relation g w579 w34 w603 true 0 6 false 68
    (by decide +kernel) (h579 g hi) (h34 g hi)

theorem h604 : eval g w604 = 1 := by
  exact rewrite_relation g w603 w34 w604 true 0 18 false 55
    (by decide +kernel) (h603 g hi) (h34 g hi)

theorem h605 : eval g w605 = 1 := by
  exact rewrite_relation g w604 w34 w605 false 0 49 false 23
    (by decide +kernel) (h604 g hi) (h34 g hi)

theorem h606 : eval g w606 = 1 := by
  exact rewrite_relation g w605 w34 w606 false 0 55 false 16
    (by decide +kernel) (h605 g hi) (h34 g hi)

theorem h607 : eval g w607 = 1 := by
  exact rewrite_relation g w590 w34 w607 false 0 5 false 25
    (by decide +kernel) (h590 g hi) (h34 g hi)

theorem h608 : eval g w608 = 1 := by
  exact rewrite_relation g w494 w34 w608 false 0 5 false 17
    (by decide +kernel) (h494 g hi) (h34 g hi)

theorem h609 : eval g w609 = 1 := by
  exact rewrite_relation g w586 w34 w609 false 0 4 false 64
    (by decide +kernel) (h586 g hi) (h34 g hi)

theorem h610 : eval g w610 = 1 := by
  exact rewrite_relation g w607 w34 w610 true 0 16 false 52
    (by decide +kernel) (h607 g hi) (h34 g hi)

theorem h611 : eval g w611 = 1 := by
  exact rewrite_relation g w608 w34 w611 false 0 5 false 17
    (by decide +kernel) (h608 g hi) (h34 g hi)

theorem h612 : eval g w612 = 1 := by
  exact rewrite_relation g w609 w34 w612 false 0 26 false 41
    (by decide +kernel) (h609 g hi) (h34 g hi)

theorem h613 : eval g w613 = 1 := by
  exact rewrite_relation g w610 w34 w613 false 0 20 false 47
    (by decide +kernel) (h610 g hi) (h34 g hi)

theorem h614 : eval g w614 = 1 := by
  exact rewrite_relation g w596 w34 w614 false 0 57 false 9
    (by decide +kernel) (h596 g hi) (h34 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
