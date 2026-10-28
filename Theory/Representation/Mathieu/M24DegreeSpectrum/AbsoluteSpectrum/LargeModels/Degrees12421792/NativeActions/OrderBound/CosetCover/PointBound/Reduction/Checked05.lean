module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked04

/-!
# Checked Tietze relations (block 5)

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

theorem h460 : eval g w460 = 1 := by
  exact substitution_relation g 18 replacement19 w448 w460 false 0
    (by decide +kernel) (eq19 g hi) (h448 g hi)

theorem h461 : eval g w461 = 1 := by
  exact substitution_relation g 18 replacement19 w449 w461 false 0
    (by decide +kernel) (eq19 g hi) (h449 g hi)

theorem h463 : eval g w463 = 1 := by
  exact substitution_relation g 18 replacement19 w451 w463 false 0
    (by decide +kernel) (eq19 g hi) (h451 g hi)

theorem h464 : eval g w464 = 1 := by
  exact substitution_relation g 18 replacement19 w453 w464 false 0
    (by decide +kernel) (eq19 g hi) (h453 g hi)

theorem h465 : eval g w465 = 1 := by
  exact substitution_relation g 18 replacement19 w454 w465 false 0
    (by decide +kernel) (eq19 g hi) (h454 g hi)

theorem h467 : eval g w467 = 1 := by
  exact substitution_relation g 18 replacement19 w358 w467 false 6
    (by decide +kernel) (eq19 g hi) (h358 g hi)

theorem h468 : eval g w468 = 1 := by
  exact substitution_relation g 5 replacement6 w455 w468 false 19
    (by decide +kernel) (eq6 g hi) (h455 g hi)

theorem h469 : eval g w469 = 1 := by
  exact substitution_relation g 5 replacement6 w456 w469 false 4
    (by decide +kernel) (eq6 g hi) (h456 g hi)

theorem h470 : eval g w470 = 1 := by
  exact substitution_relation g 5 replacement6 w457 w470 false 4
    (by decide +kernel) (eq6 g hi) (h457 g hi)

theorem h471 : eval g w471 = 1 := by
  exact substitution_relation g 5 replacement6 w458 w471 false 0
    (by decide +kernel) (eq6 g hi) (h458 g hi)

theorem h472 : eval g w472 = 1 := by
  exact substitution_relation g 5 replacement6 w436 w472 true 19
    (by decide +kernel) (eq6 g hi) (h436 g hi)

theorem h473 : eval g w473 = 1 := by
  exact substitution_relation g 5 replacement6 w459 w473 false 4
    (by decide +kernel) (eq6 g hi) (h459 g hi)

theorem h474 : eval g w474 = 1 := by
  exact substitution_relation g 5 replacement6 w460 w474 false 0
    (by decide +kernel) (eq6 g hi) (h460 g hi)

theorem h475 : eval g w475 = 1 := by
  exact substitution_relation g 5 replacement6 w461 w475 false 0
    (by decide +kernel) (eq6 g hi) (h461 g hi)

theorem h477 : eval g w477 = 1 := by
  exact substitution_relation g 5 replacement6 w63 w477 false 2
    (by decide +kernel) (eq6 g hi) (h63 g hi)

theorem h478 : eval g w478 = 1 := by
  exact substitution_relation g 5 replacement6 w463 w478 false 4
    (by decide +kernel) (eq6 g hi) (h463 g hi)

theorem h479 : eval g w479 = 1 := by
  exact substitution_relation g 5 replacement6 w439 w479 true 13
    (by decide +kernel) (eq6 g hi) (h439 g hi)

theorem h480 : eval g w480 = 1 := by
  exact substitution_relation g 5 replacement6 w464 w480 true 8
    (by decide +kernel) (eq6 g hi) (h464 g hi)

theorem h481 : eval g w481 = 1 := by
  exact substitution_relation g 5 replacement6 w465 w481 false 4
    (by decide +kernel) (eq6 g hi) (h465 g hi)

theorem h483 : eval g w483 = 1 := by
  exact substitution_relation g 5 replacement6 w441 w483 false 3
    (by decide +kernel) (eq6 g hi) (h441 g hi)

theorem h484 : eval g w484 = 1 := by
  exact substitution_relation g 5 replacement6 w467 w484 false 12
    (by decide +kernel) (eq6 g hi) (h467 g hi)

theorem h485 : eval g w485 = 1 := by
  exact substitution_relation g 5 replacement6 w143 w485 false 2
    (by decide +kernel) (eq6 g hi) (h143 g hi)

theorem h486 : eval g w486 = 1 := by
  exact substitution_relation g 1 replacement2 w468 w486 true 9
    (by decide +kernel) (eq2 g hi) (h468 g hi)

theorem h487 : eval g w487 = 1 := by
  exact substitution_relation g 1 replacement2 w469 w487 true 48
    (by decide +kernel) (eq2 g hi) (h469 g hi)

theorem h488 : eval g w488 = 1 := by
  exact substitution_relation g 1 replacement2 w470 w488 false 133
    (by decide +kernel) (eq2 g hi) (h470 g hi)

theorem h489 : eval g w489 = 1 := by
  exact substitution_relation g 1 replacement2 w471 w489 false 0
    (by decide +kernel) (eq2 g hi) (h471 g hi)

theorem h490 : eval g w490 = 1 := by
  exact substitution_relation g 1 replacement2 w472 w490 true 55
    (by decide +kernel) (eq2 g hi) (h472 g hi)

theorem h491 : eval g w491 = 1 := by
  exact substitution_relation g 1 replacement2 w473 w491 false 75
    (by decide +kernel) (eq2 g hi) (h473 g hi)

theorem h492 : eval g w492 = 1 := by
  exact substitution_relation g 1 replacement2 w474 w492 true 1
    (by decide +kernel) (eq2 g hi) (h474 g hi)

theorem h493 : eval g w493 = 1 := by
  exact substitution_relation g 1 replacement2 w475 w493 false 91
    (by decide +kernel) (eq2 g hi) (h475 g hi)

theorem h494 : eval g w494 = 1 := by
  exact substitution_relation g 1 replacement2 w477 w494 false 20
    (by decide +kernel) (eq2 g hi) (h477 g hi)

theorem h495 : eval g w495 = 1 := by
  exact substitution_relation g 1 replacement2 w478 w495 false 130
    (by decide +kernel) (eq2 g hi) (h478 g hi)

theorem h496 : eval g w496 = 1 := by
  exact substitution_relation g 1 replacement2 w479 w496 true 24
    (by decide +kernel) (eq2 g hi) (h479 g hi)

theorem h497 : eval g w497 = 1 := by
  exact substitution_relation g 1 replacement2 w452 w497 false 3
    (by decide +kernel) (eq2 g hi) (h452 g hi)

theorem h498 : eval g w498 = 1 := by
  exact substitution_relation g 1 replacement2 w480 w498 true 17
    (by decide +kernel) (eq2 g hi) (h480 g hi)

theorem h499 : eval g w499 = 1 := by
  exact substitution_relation g 1 replacement2 w481 w499 false 40
    (by decide +kernel) (eq2 g hi) (h481 g hi)

theorem h501 : eval g w501 = 1 := by
  exact substitution_relation g 1 replacement2 w483 w501 false 12
    (by decide +kernel) (eq2 g hi) (h483 g hi)

theorem h502 : eval g w502 = 1 := by
  exact substitution_relation g 1 replacement2 w484 w502 false 86
    (by decide +kernel) (eq2 g hi) (h484 g hi)

theorem h503 : eval g w503 = 1 := by
  exact substitution_relation g 1 replacement2 w485 w503 false 12
    (by decide +kernel) (eq2 g hi) (h485 g hi)

theorem h504 : eval g w504 = 1 := by
  exact rewrite_relation g w498 w496 w504 false 9 0 true 277
    (by decide +kernel) (h498 g hi) (h496 g hi)

theorem h505 : eval g w505 = 1 := by
  exact rewrite_relation g w504 w34 w505 false 0 3 false 20
    (by decide +kernel) (h504 g hi) (h34 g hi)

theorem h506 : eval g w506 = 1 := by
  exact rewrite_relation g w505 w34 w506 false 0 3 true 35
    (by decide +kernel) (h505 g hi) (h34 g hi)

theorem h507 : eval g w507 = 1 := by
  exact rewrite_relation g w506 w496 w507 false 9 0 true 250
    (by decide +kernel) (h506 g hi) (h496 g hi)

theorem h508 : eval g w508 = 1 := by
  exact rewrite_relation g w507 w34 w508 false 0 3 false 20
    (by decide +kernel) (h507 g hi) (h34 g hi)

theorem h509 : eval g w509 = 1 := by
  exact rewrite_relation g w508 w34 w509 false 0 3 true 35
    (by decide +kernel) (h508 g hi) (h34 g hi)

theorem h510 : eval g w510 = 1 := by
  exact rewrite_relation g w509 w496 w510 false 9 0 true 223
    (by decide +kernel) (h509 g hi) (h496 g hi)

theorem h511 : eval g w511 = 1 := by
  exact rewrite_relation g w495 w489 w511 true 8 0 false 8
    (by decide +kernel) (h495 g hi) (h489 g hi)

theorem h512 : eval g w512 = 1 := by
  exact rewrite_relation g w510 w34 w512 false 0 3 false 20
    (by decide +kernel) (h510 g hi) (h34 g hi)

theorem h513 : eval g w513 = 1 := by
  exact rewrite_relation g w512 w34 w513 false 0 3 true 35
    (by decide +kernel) (h512 g hi) (h34 g hi)

theorem h514 : eval g w514 = 1 := by
  exact rewrite_relation g w513 w496 w514 false 9 0 true 196
    (by decide +kernel) (h513 g hi) (h496 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
