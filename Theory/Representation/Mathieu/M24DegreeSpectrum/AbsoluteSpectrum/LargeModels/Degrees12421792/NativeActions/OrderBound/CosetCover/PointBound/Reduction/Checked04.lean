module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked03

/-!
# Checked Tietze relations (block 4)

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

theorem h384 : eval g w384 = 1 := by
  exact substitution_relation g 21 replacement22 w362 w384 false 0
    (by decide +kernel) (eq22 g hi) (h362 g hi)

theorem h385 : eval g w385 = 1 := by
  exact substitution_relation g 21 replacement22 w363 w385 false 0
    (by decide +kernel) (eq22 g hi) (h363 g hi)

theorem h386 : eval g w386 = 1 := by
  exact substitution_relation g 21 replacement22 w364 w386 false 0
    (by decide +kernel) (eq22 g hi) (h364 g hi)

theorem h388 : eval g w388 = 1 := by
  exact substitution_relation g 21 replacement22 w366 w388 false 0
    (by decide +kernel) (eq22 g hi) (h366 g hi)

theorem h390 : eval g w390 = 1 := by
  exact substitution_relation g 21 replacement22 w368 w390 false 0
    (by decide +kernel) (eq22 g hi) (h368 g hi)

theorem h392 : eval g w392 = 1 := by
  exact substitution_relation g 21 replacement22 w370 w392 false 0
    (by decide +kernel) (eq22 g hi) (h370 g hi)

theorem h394 : eval g w394 = 1 := by
  exact substitution_relation g 21 replacement22 w372 w394 false 0
    (by decide +kernel) (eq22 g hi) (h372 g hi)

theorem h398 : eval g w398 = 1 := by
  exact substitution_relation g 21 replacement22 w377 w398 false 0
    (by decide +kernel) (eq22 g hi) (h377 g hi)

theorem h403 : eval g w403 = 1 := by
  exact substitution_relation g 23 replacement24 w384 w403 false 0
    (by decide +kernel) (eq24 g hi) (h384 g hi)

theorem h404 : eval g w404 = 1 := by
  exact substitution_relation g 23 replacement24 w385 w404 false 0
    (by decide +kernel) (eq24 g hi) (h385 g hi)

theorem h405 : eval g w405 = 1 := by
  exact substitution_relation g 23 replacement24 w386 w405 false 0
    (by decide +kernel) (eq24 g hi) (h386 g hi)

theorem h407 : eval g w407 = 1 := by
  exact substitution_relation g 23 replacement24 w388 w407 true 9
    (by decide +kernel) (eq24 g hi) (h388 g hi)

theorem h410 : eval g w410 = 1 := by
  exact substitution_relation g 23 replacement24 w390 w410 false 0
    (by decide +kernel) (eq24 g hi) (h390 g hi)

theorem h412 : eval g w412 = 1 := by
  exact substitution_relation g 23 replacement24 w392 w412 false 0
    (by decide +kernel) (eq24 g hi) (h392 g hi)

theorem h413 : eval g w413 = 1 := by
  exact substitution_relation g 23 replacement24 w23 w413 false 0
    (by decide +kernel) (eq24 g hi) (h23 g hi)

theorem h415 : eval g w415 = 1 := by
  exact substitution_relation g 23 replacement24 w394 w415 false 0
    (by decide +kernel) (eq24 g hi) (h394 g hi)

theorem h417 : eval g w417 = 1 := by
  exact substitution_relation g 23 replacement24 w398 w417 false 0
    (by decide +kernel) (eq24 g hi) (h398 g hi)

theorem eq17 : g 16 = eval g replacement17 :=
  generator_equation g 16 replacement17 w417 false 2
    (by decide +kernel) (h417 g hi)

theorem h422 : eval g w422 = 1 := by
  exact substitution_relation g 22 replacement23 w383 w422 true 6
    (by decide +kernel) (eq23 g hi) (h383 g hi)

theorem h423 : eval g w423 = 1 := by
  exact substitution_relation g 22 replacement23 w403 w423 false 7
    (by decide +kernel) (eq23 g hi) (h403 g hi)

theorem h424 : eval g w424 = 1 := by
  exact substitution_relation g 22 replacement23 w405 w424 false 6
    (by decide +kernel) (eq23 g hi) (h405 g hi)

theorem h426 : eval g w426 = 1 := by
  exact substitution_relation g 22 replacement23 w407 w426 true 8
    (by decide +kernel) (eq23 g hi) (h407 g hi)

theorem h427 : eval g w427 = 1 := by
  exact substitution_relation g 22 replacement23 w410 w427 false 0
    (by decide +kernel) (eq23 g hi) (h410 g hi)

theorem h428 : eval g w428 = 1 := by
  exact substitution_relation g 22 replacement23 w412 w428 false 0
    (by decide +kernel) (eq23 g hi) (h412 g hi)

theorem h429 : eval g w429 = 1 := by
  exact substitution_relation g 22 replacement23 w415 w429 false 0
    (by decide +kernel) (eq23 g hi) (h415 g hi)

theorem h431 : eval g w431 = 1 := by
  exact substitution_relation g 8 replacement9 w422 w431 false 0
    (by decide +kernel) (eq9 g hi) (h422 g hi)

theorem h432 : eval g w432 = 1 := by
  exact substitution_relation g 8 replacement9 w423 w432 false 0
    (by decide +kernel) (eq9 g hi) (h423 g hi)

theorem h433 : eval g w433 = 1 := by
  exact substitution_relation g 8 replacement9 w215 w433 false 0
    (by decide +kernel) (eq9 g hi) (h215 g hi)

theorem h434 : eval g w434 = 1 := by
  exact substitution_relation g 8 replacement9 w404 w434 false 0
    (by decide +kernel) (eq9 g hi) (h404 g hi)

theorem h435 : eval g w435 = 1 := by
  exact substitution_relation g 8 replacement9 w424 w435 false 0
    (by decide +kernel) (eq9 g hi) (h424 g hi)

theorem h436 : eval g w436 = 1 := by
  exact substitution_relation g 8 replacement9 w426 w436 false 0
    (by decide +kernel) (eq9 g hi) (h426 g hi)

theorem h437 : eval g w437 = 1 := by
  exact substitution_relation g 8 replacement9 w427 w437 false 0
    (by decide +kernel) (eq9 g hi) (h427 g hi)

theorem h438 : eval g w438 = 1 := by
  exact substitution_relation g 8 replacement9 w429 w438 false 0
    (by decide +kernel) (eq9 g hi) (h429 g hi)

theorem eq2 : g 1 = eval g replacement2 :=
  generator_equation g 1 replacement2 w438 false 8
    (by decide +kernel) (h438 g hi)

theorem h439 : eval g w439 = 1 := by
  exact substitution_relation g 8 replacement9 w176 w439 false 6
    (by decide +kernel) (eq9 g hi) (h176 g hi)

theorem h441 : eval g w441 = 1 := by
  exact substitution_relation g 8 replacement9 w380 w441 false 1
    (by decide +kernel) (eq9 g hi) (h380 g hi)

theorem h443 : eval g w443 = 1 := by
  exact substitution_relation g 16 replacement17 w431 w443 true 4
    (by decide +kernel) (eq17 g hi) (h431 g hi)

theorem h444 : eval g w444 = 1 := by
  exact substitution_relation g 16 replacement17 w432 w444 true 2
    (by decide +kernel) (eq17 g hi) (h432 g hi)

theorem h445 : eval g w445 = 1 := by
  exact substitution_relation g 16 replacement17 w433 w445 false 8
    (by decide +kernel) (eq17 g hi) (h433 g hi)

theorem eq6 : g 5 = eval g replacement6 :=
  generator_equation g 5 replacement6 w445 false 7
    (by decide +kernel) (h445 g hi)

theorem h446 : eval g w446 = 1 := by
  exact substitution_relation g 16 replacement17 w434 w446 false 5
    (by decide +kernel) (eq17 g hi) (h434 g hi)

theorem h447 : eval g w447 = 1 := by
  exact substitution_relation g 16 replacement17 w349 w447 true 2
    (by decide +kernel) (eq17 g hi) (h349 g hi)

theorem h448 : eval g w448 = 1 := by
  exact substitution_relation g 16 replacement17 w437 w448 false 0
    (by decide +kernel) (eq17 g hi) (h437 g hi)

theorem h449 : eval g w449 = 1 := by
  exact substitution_relation g 16 replacement17 w428 w449 false 14
    (by decide +kernel) (eq17 g hi) (h428 g hi)

theorem h451 : eval g w451 = 1 := by
  exact substitution_relation g 16 replacement17 w354 w451 false 5
    (by decide +kernel) (eq17 g hi) (h354 g hi)

theorem h452 : eval g w452 = 1 := by
  exact substitution_relation g 16 replacement17 w43 w452 false 2
    (by decide +kernel) (eq17 g hi) (h43 g hi)

theorem h453 : eval g w453 = 1 := by
  exact substitution_relation g 16 replacement17 w336 w453 true 2
    (by decide +kernel) (eq17 g hi) (h336 g hi)

theorem h454 : eval g w454 = 1 := by
  exact substitution_relation g 16 replacement17 w356 w454 false 5
    (by decide +kernel) (eq17 g hi) (h356 g hi)

theorem h455 : eval g w455 = 1 := by
  exact substitution_relation g 18 replacement19 w443 w455 false 0
    (by decide +kernel) (eq19 g hi) (h443 g hi)

theorem h456 : eval g w456 = 1 := by
  exact substitution_relation g 18 replacement19 w444 w456 false 0
    (by decide +kernel) (eq19 g hi) (h444 g hi)

theorem h457 : eval g w457 = 1 := by
  exact substitution_relation g 18 replacement19 w446 w457 false 0
    (by decide +kernel) (eq19 g hi) (h446 g hi)

theorem h458 : eval g w458 = 1 := by
  exact substitution_relation g 18 replacement19 w435 w458 false 0
    (by decide +kernel) (eq19 g hi) (h435 g hi)

theorem h459 : eval g w459 = 1 := by
  exact substitution_relation g 18 replacement19 w447 w459 false 0
    (by decide +kernel) (eq19 g hi) (h447 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
