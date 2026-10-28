module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked07

/-!
# Checked Tietze relations (block 8)

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

theorem h615 : eval g w615 = 1 := by
  exact rewrite_relation g w611 w34 w615 false 0 5 false 17
    (by decide +kernel) (h611 g hi) (h34 g hi)

theorem h616 : eval g w616 = 1 := by
  exact rewrite_relation g w612 w34 w616 false 0 30 false 36
    (by decide +kernel) (h612 g hi) (h34 g hi)

theorem h617 : eval g w617 = 1 := by
  exact rewrite_relation g w613 w615 w617 false 5 20 true 21
    (by decide +kernel) (h613 g hi) (h615 g hi)

theorem h618 : eval g w618 = 1 := by
  exact rewrite_relation g w616 w34 w618 false 0 32 false 33
    (by decide +kernel) (h616 g hi) (h34 g hi)

theorem h619 : eval g w619 = 1 := by
  exact rewrite_relation g w501 w34 w619 false 0 3 false 28
    (by decide +kernel) (h501 g hi) (h34 g hi)

theorem h620 : eval g w620 = 1 := by
  exact rewrite_relation g w588 w34 w620 false 0 17 false 46
    (by decide +kernel) (h588 g hi) (h34 g hi)

theorem h621 : eval g w621 = 1 := by
  exact rewrite_relation g w619 w34 w621 false 0 3 false 13
    (by decide +kernel) (h619 g hi) (h34 g hi)

theorem h622 : eval g w622 = 1 := by
  exact rewrite_relation g w620 w497 w622 true 2 13 false 44
    (by decide +kernel) (h620 g hi) (h497 g hi)

theorem h623 : eval g w623 = 1 := by
  exact rewrite_relation g w621 w34 w623 false 0 5 false 25
    (by decide +kernel) (h621 g hi) (h34 g hi)

theorem h624 : eval g w624 = 1 := by
  exact rewrite_relation g w567 w572 w624 false 5 6 true 20
    (by decide +kernel) (h567 g hi) (h572 g hi)

theorem h625 : eval g w625 = 1 := by
  exact rewrite_relation g w623 w34 w625 false 0 5 false 25
    (by decide +kernel) (h623 g hi) (h34 g hi)

theorem h626 : eval g w626 = 1 := by
  exact rewrite_relation g w572 w34 w626 true 0 6 false 51
    (by decide +kernel) (h572 g hi) (h34 g hi)

theorem h627 : eval g w627 = 1 := by
  exact rewrite_relation g w622 w34 w627 true 0 43 false 13
    (by decide +kernel) (h622 g hi) (h34 g hi)

theorem h628 : eval g w628 = 1 := by
  exact rewrite_relation g w530 w627 w628 true 1 22 false 1
    (by decide +kernel) (h530 g hi) (h627 g hi)

theorem h629 : eval g w629 = 1 := by
  exact rewrite_relation g w628 w585 w629 true 17 15 false 155
    (by decide +kernel) (h628 g hi) (h585 g hi)

theorem h630 : eval g w630 = 1 := by
  exact rewrite_relation g w629 w34 w630 false 0 14 false 155
    (by decide +kernel) (h629 g hi) (h34 g hi)

theorem h631 : eval g w631 = 1 := by
  exact rewrite_relation g w630 w627 w631 true 1 15 false 1
    (by decide +kernel) (h630 g hi) (h627 g hi)

theorem h632 : eval g w632 = 1 := by
  exact rewrite_relation g w631 w34 w632 false 0 18 false 134
    (by decide +kernel) (h631 g hi) (h34 g hi)

theorem h633 : eval g w633 = 1 := by
  exact rewrite_relation g w632 w627 w633 true 1 21 false 1
    (by decide +kernel) (h632 g hi) (h627 g hi)

theorem h634 : eval g w634 = 1 := by
  exact rewrite_relation g w633 w585 w634 true 17 15 false 95
    (by decide +kernel) (h633 g hi) (h585 g hi)

theorem h635 : eval g w635 = 1 := by
  exact rewrite_relation g w634 w34 w635 true 0 20 false 111
    (by decide +kernel) (h634 g hi) (h34 g hi)

theorem h636 : eval g w636 = 1 := by
  exact rewrite_relation g w635 w34 w636 false 0 35 false 95
    (by decide +kernel) (h635 g hi) (h34 g hi)

theorem h637 : eval g w637 = 1 := by
  exact rewrite_relation g w636 w627 w637 true 1 36 false 1
    (by decide +kernel) (h636 g hi) (h627 g hi)

theorem h638 : eval g w638 = 1 := by
  exact rewrite_relation g w637 w34 w638 false 0 18 false 58
    (by decide +kernel) (h637 g hi) (h34 g hi)

theorem h639 : eval g w639 = 1 := by
  exact rewrite_relation g w638 w34 w639 true 0 35 false 98
    (by decide +kernel) (h638 g hi) (h34 g hi)

theorem h640 : eval g w640 = 1 := by
  exact rewrite_relation g w639 w627 w640 true 1 36 false 60
    (by decide +kernel) (h639 g hi) (h627 g hi)

theorem h641 : eval g w641 = 1 := by
  exact rewrite_relation g w640 w34 w641 true 0 35 false 60
    (by decide +kernel) (h640 g hi) (h34 g hi)

theorem h642 : eval g w642 = 1 := by
  exact rewrite_relation g w641 w34 w642 true 0 56 false 38
    (by decide +kernel) (h641 g hi) (h34 g hi)

theorem h643 : eval g w643 = 1 := by
  exact rewrite_relation g w642 w497 w643 false 4 49 false 77
    (by decide +kernel) (h642 g hi) (h497 g hi)

theorem h644 : eval g w644 = 1 := by
  exact rewrite_relation g w643 w34 w644 true 0 31 false 58
    (by decide +kernel) (h643 g hi) (h34 g hi)

theorem h645 : eval g w645 = 1 := by
  exact rewrite_relation g w585 w627 w645 false 18 20 true 44
    (by decide +kernel) (h585 g hi) (h627 g hi)

theorem h646 : eval g w646 = 1 := by
  exact rewrite_relation g w645 w627 w646 false 19 18 false 20
    (by decide +kernel) (h645 g hi) (h627 g hi)

theorem h647 : eval g w647 = 1 := by
  exact rewrite_relation g w644 w646 w647 false 0 32 false 55
    (by decide +kernel) (h644 g hi) (h646 g hi)

theorem h648 : eval g w648 = 1 := by
  exact rewrite_relation g w647 w34 w648 false 0 31 false 53
    (by decide +kernel) (h647 g hi) (h34 g hi)

theorem h649 : eval g w649 = 1 := by
  exact rewrite_relation g w648 w646 w649 false 0 61 false 19
    (by decide +kernel) (h648 g hi) (h646 g hi)

theorem h650 : eval g w650 = 1 := by
  exact rewrite_relation g w649 w34 w650 false 0 60 false 63
    (by decide +kernel) (h649 g hi) (h34 g hi)

theorem h651 : eval g w651 = 1 := by
  exact rewrite_relation g w626 w34 w651 true 0 18 false 38
    (by decide +kernel) (h626 g hi) (h34 g hi)

theorem h652 : eval g w652 = 1 := by
  exact rewrite_relation g w651 w34 w652 true 0 28 false 27
    (by decide +kernel) (h651 g hi) (h34 g hi)

theorem h653 : eval g w653 = 1 := by
  exact rewrite_relation g w625 w652 w653 true 23 22 false 23
    (by decide +kernel) (h625 g hi) (h652 g hi)

theorem h654 : eval g w654 = 1 := by
  exact rewrite_relation g w653 w652 w654 true 23 4 false 23
    (by decide +kernel) (h653 g hi) (h652 g hi)

theorem h655 : eval g w655 = 1 := by
  exact rewrite_relation g w627 w652 w655 false 4 19 false 18
    (by decide +kernel) (h627 g hi) (h652 g hi)

theorem h656 : eval g w656 = 1 := by
  exact rewrite_relation g w652 w34 w656 true 0 40 false 14
    (by decide +kernel) (h652 g hi) (h34 g hi)

theorem h657 : eval g w657 = 1 := by
  exact rewrite_relation g w654 w34 w657 false 0 3 false 23
    (by decide +kernel) (h654 g hi) (h34 g hi)

theorem h658 : eval g w658 = 1 := by
  exact rewrite_relation g w657 w34 w658 false 0 3 true 11
    (by decide +kernel) (h657 g hi) (h34 g hi)

theorem h659 : eval g w659 = 1 := by
  exact rewrite_relation g w658 w34 w659 false 0 5 false 20
    (by decide +kernel) (h658 g hi) (h34 g hi)

theorem h660 : eval g w660 = 1 := by
  exact rewrite_relation g w659 w34 w660 false 0 5 false 20
    (by decide +kernel) (h659 g hi) (h34 g hi)

theorem h661 : eval g w661 = 1 := by
  exact rewrite_relation g w617 w34 w661 false 0 3 true 4
    (by decide +kernel) (h617 g hi) (h34 g hi)

theorem h662 : eval g w662 = 1 := by
  exact rewrite_relation g w606 w661 w662 true 45 23 false 46
    (by decide +kernel) (h606 g hi) (h661 g hi)

theorem h663 : eval g w663 = 1 := by
  exact rewrite_relation g w662 w34 w663 false 0 22 false 46
    (by decide +kernel) (h662 g hi) (h34 g hi)

theorem h664 : eval g w664 = 1 := by
  exact rewrite_relation g w618 w661 w664 true 1 27 false 30
    (by decide +kernel) (h618 g hi) (h661 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
