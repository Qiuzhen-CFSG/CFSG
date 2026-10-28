module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked08

/-!
# Checked Tietze relations (block 9)

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

theorem h665 : eval g w665 = 1 := by
  exact rewrite_relation g w664 w34 w665 true 0 26 false 30
    (by decide +kernel) (h664 g hi) (h34 g hi)

theorem h666 : eval g w666 = 1 := by
  exact rewrite_relation g w665 w497 w666 false 4 19 true 40
    (by decide +kernel) (h665 g hi) (h497 g hi)

theorem h667 : eval g w667 = 1 := by
  exact rewrite_relation g w646 w655 w667 true 15 15 false 22
    (by decide +kernel) (h646 g hi) (h655 g hi)

theorem h668 : eval g w668 = 1 := by
  exact rewrite_relation g w655 w497 w668 false 4 29 true 6
    (by decide +kernel) (h655 g hi) (h497 g hi)

theorem h669 : eval g w669 = 1 := by
  exact rewrite_relation g w650 w668 w669 true 3 39 false 29
    (by decide +kernel) (h650 g hi) (h668 g hi)

theorem h670 : eval g w670 = 1 := by
  exact rewrite_relation g w669 w668 w670 true 6 46 false 55
    (by decide +kernel) (h669 g hi) (h668 g hi)

theorem h671 : eval g w671 = 1 := by
  exact rewrite_relation g w667 w497 w671 false 4 22 false 7
    (by decide +kernel) (h667 g hi) (h497 g hi)

theorem h672 : eval g w672 = 1 := by
  exact rewrite_relation g w668 w624 w672 false 14 22 false 3
    (by decide +kernel) (h668 g hi) (h624 g hi)

theorem h673 : eval g w673 = 1 := by
  exact rewrite_relation g w670 w672 w673 true 4 30 false 27
    (by decide +kernel) (h670 g hi) (h672 g hi)

theorem h674 : eval g w674 = 1 := by
  exact rewrite_relation g w671 w34 w674 true 0 26 true 16
    (by decide +kernel) (h671 g hi) (h34 g hi)

theorem h675 : eval g w675 = 1 := by
  exact rewrite_relation g w566 w674 w675 false 0 0 true 89
    (by decide +kernel) (h566 g hi) (h674 g hi)

theorem h676 : eval g w676 = 1 := by
  exact rewrite_relation g w675 w674 w676 true 9 10 false 5
    (by decide +kernel) (h675 g hi) (h674 g hi)

theorem h677 : eval g w677 = 1 := by
  exact rewrite_relation g w676 w674 w677 true 9 10 false 5
    (by decide +kernel) (h676 g hi) (h674 g hi)

theorem h678 : eval g w678 = 1 := by
  exact rewrite_relation g w677 w674 w678 true 9 10 false 5
    (by decide +kernel) (h677 g hi) (h674 g hi)

theorem h679 : eval g w679 = 1 := by
  exact rewrite_relation g w581 w674 w679 false 19 26 true 77
    (by decide +kernel) (h581 g hi) (h674 g hi)

theorem h680 : eval g w680 = 1 := by
  exact rewrite_relation g w602 w674 w680 true 10 19 false 6
    (by decide +kernel) (h602 g hi) (h674 g hi)

theorem h681 : eval g w681 = 1 := by
  exact rewrite_relation g w679 w674 w681 true 10 27 false 51
    (by decide +kernel) (h679 g hi) (h674 g hi)

theorem h682 : eval g w682 = 1 := by
  exact rewrite_relation g w680 w674 w682 true 10 33 false 6
    (by decide +kernel) (h680 g hi) (h674 g hi)

theorem h683 : eval g w683 = 1 := by
  exact rewrite_relation g w678 w674 w683 true 9 10 false 5
    (by decide +kernel) (h678 g hi) (h674 g hi)

theorem h684 : eval g w684 = 1 := by
  exact rewrite_relation g w681 w674 w684 true 9 43 false 5
    (by decide +kernel) (h681 g hi) (h674 g hi)

theorem h685 : eval g w685 = 1 := by
  exact rewrite_relation g w591 w674 w685 false 19 25 false 50
    (by decide +kernel) (h591 g hi) (h674 g hi)

theorem h686 : eval g w686 = 1 := by
  exact rewrite_relation g w594 w674 w686 false 19 14 true 71
    (by decide +kernel) (h594 g hi) (h674 g hi)

theorem h687 : eval g w687 = 1 := by
  exact rewrite_relation g w685 w674 w687 true 10 37 false 6
    (by decide +kernel) (h685 g hi) (h674 g hi)

theorem h688 : eval g w688 = 1 := by
  exact rewrite_relation g w686 w674 w688 true 10 30 false 6
    (by decide +kernel) (h686 g hi) (h674 g hi)

theorem h689 : eval g w689 = 1 := by
  exact rewrite_relation g w687 w674 w689 true 9 10 false 16
    (by decide +kernel) (h687 g hi) (h674 g hi)

theorem h690 : eval g w690 = 1 := by
  exact rewrite_relation g w615 w674 w690 false 19 13 true 61
    (by decide +kernel) (h615 g hi) (h674 g hi)

theorem h691 : eval g w691 = 1 := by
  exact rewrite_relation g w690 w674 w691 true 10 14 false 48
    (by decide +kernel) (h690 g hi) (h674 g hi)

theorem h692 : eval g w692 = 1 := by
  exact rewrite_relation g w691 w674 w692 true 10 34 false 6
    (by decide +kernel) (h691 g hi) (h674 g hi)

theorem h693 : eval g w693 = 1 := by
  exact rewrite_relation g w673 w674 w693 true 13 20 false 35
    (by decide +kernel) (h673 g hi) (h674 g hi)

theorem h694 : eval g w694 = 1 := by
  exact rewrite_relation g w656 w674 w694 false 19 24 true 49
    (by decide +kernel) (h656 g hi) (h674 g hi)

theorem h695 : eval g w695 = 1 := by
  exact rewrite_relation g w661 w674 w695 true 10 23 false 6
    (by decide +kernel) (h661 g hi) (h674 g hi)

theorem h696 : eval g w696 = 1 := by
  exact rewrite_relation g w666 w674 w696 true 13 13 false 31
    (by decide +kernel) (h666 g hi) (h674 g hi)

theorem h697 : eval g w697 = 1 := by
  exact rewrite_relation g w696 w34 w697 false 0 12 false 31
    (by decide +kernel) (h696 g hi) (h34 g hi)

theorem h698 : eval g w698 = 1 := by
  exact rewrite_relation g w672 w674 w698 false 15 11 true 12
    (by decide +kernel) (h672 g hi) (h674 g hi)

theorem h699 : eval g w699 = 1 := by
  exact rewrite_relation g w682 w698 w699 false 0 1 false 36
    (by decide +kernel) (h682 g hi) (h698 g hi)

theorem h700 : eval g w700 = 1 := by
  exact rewrite_relation g w699 w698 w700 false 0 1 false 1
    (by decide +kernel) (h699 g hi) (h698 g hi)

theorem h701 : eval g w701 = 1 := by
  exact rewrite_relation g w693 w698 w701 false 0 1 false 37
    (by decide +kernel) (h693 g hi) (h698 g hi)

theorem h702 : eval g w702 = 1 := by
  exact rewrite_relation g w701 w34 w702 true 0 22 false 28
    (by decide +kernel) (h701 g hi) (h34 g hi)

theorem h703 : eval g w703 = 1 := by
  exact rewrite_relation g w702 w698 w703 true 20 37 false 11
    (by decide +kernel) (h702 g hi) (h698 g hi)

theorem h704 : eval g w704 = 1 := by
  exact rewrite_relation g w703 w674 w704 false 7 28 false 39
    (by decide +kernel) (h703 g hi) (h674 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
