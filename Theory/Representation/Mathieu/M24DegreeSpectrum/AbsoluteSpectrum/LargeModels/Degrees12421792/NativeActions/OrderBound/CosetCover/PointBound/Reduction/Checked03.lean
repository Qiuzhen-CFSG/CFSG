module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked02

/-!
# Checked Tietze relations (block 3)

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

theorem h287 : eval g w287 = 1 := by
  exact substitution_relation g 13 replacement14 w214 w287 false 0
    (by decide +kernel) (eq14 g hi) (h214 g hi)

theorem h288 : eval g w288 = 1 := by
  exact substitution_relation g 13 replacement14 w263 w288 false 0
    (by decide +kernel) (eq14 g hi) (h263 g hi)

theorem h290 : eval g w290 = 1 := by
  exact substitution_relation g 13 replacement14 w240 w290 false 0
    (by decide +kernel) (eq14 g hi) (h240 g hi)

theorem h291 : eval g w291 = 1 := by
  exact substitution_relation g 13 replacement14 w269 w291 false 0
    (by decide +kernel) (eq14 g hi) (h269 g hi)

theorem h293 : eval g w293 = 1 := by
  exact substitution_relation g 13 replacement14 w272 w293 false 0
    (by decide +kernel) (eq14 g hi) (h272 g hi)

theorem h296 : eval g w296 = 1 := by
  exact substitution_relation g 13 replacement14 w248 w296 false 0
    (by decide +kernel) (eq14 g hi) (h248 g hi)

theorem h298 : eval g w298 = 1 := by
  exact substitution_relation g 13 replacement14 w44 w298 false 0
    (by decide +kernel) (eq14 g hi) (h44 g hi)

theorem h299 : eval g w299 = 1 := by
  exact substitution_relation g 13 replacement14 w252 w299 false 0
    (by decide +kernel) (eq14 g hi) (h252 g hi)

theorem h302 : eval g w302 = 1 := by
  exact substitution_relation g 14 replacement15 w286 w302 false 0
    (by decide +kernel) (eq15 g hi) (h286 g hi)

theorem h303 : eval g w303 = 1 := by
  exact substitution_relation g 14 replacement15 w287 w303 false 0
    (by decide +kernel) (eq15 g hi) (h287 g hi)

theorem h304 : eval g w304 = 1 := by
  exact substitution_relation g 14 replacement15 w288 w304 false 0
    (by decide +kernel) (eq15 g hi) (h288 g hi)

theorem h305 : eval g w305 = 1 := by
  exact substitution_relation g 14 replacement15 w264 w305 false 0
    (by decide +kernel) (eq15 g hi) (h264 g hi)

theorem h307 : eval g w307 = 1 := by
  exact substitution_relation g 14 replacement15 w266 w307 false 0
    (by decide +kernel) (eq15 g hi) (h266 g hi)

theorem h310 : eval g w310 = 1 := by
  exact substitution_relation g 14 replacement15 w291 w310 false 0
    (by decide +kernel) (eq15 g hi) (h291 g hi)

theorem h312 : eval g w312 = 1 := by
  exact substitution_relation g 14 replacement15 w293 w312 false 0
    (by decide +kernel) (eq15 g hi) (h293 g hi)

theorem h314 : eval g w314 = 1 := by
  exact substitution_relation g 14 replacement15 w274 w314 false 0
    (by decide +kernel) (eq15 g hi) (h274 g hi)

theorem h317 : eval g w317 = 1 := by
  exact substitution_relation g 14 replacement15 w279 w317 false 0
    (by decide +kernel) (eq15 g hi) (h279 g hi)

theorem h321 : eval g w321 = 1 := by
  exact substitution_relation g 15 replacement16 w302 w321 false 0
    (by decide +kernel) (eq16 g hi) (h302 g hi)

theorem h322 : eval g w322 = 1 := by
  exact substitution_relation g 15 replacement16 w303 w322 false 0
    (by decide +kernel) (eq16 g hi) (h303 g hi)

theorem h323 : eval g w323 = 1 := by
  exact substitution_relation g 15 replacement16 w304 w323 false 0
    (by decide +kernel) (eq16 g hi) (h304 g hi)

theorem h325 : eval g w325 = 1 := by
  exact substitution_relation g 15 replacement16 w290 w325 false 0
    (by decide +kernel) (eq16 g hi) (h290 g hi)

theorem h326 : eval g w326 = 1 := by
  exact substitution_relation g 15 replacement16 w310 w326 false 0
    (by decide +kernel) (eq16 g hi) (h310 g hi)

theorem h329 : eval g w329 = 1 := by
  exact substitution_relation g 15 replacement16 w312 w329 false 0
    (by decide +kernel) (eq16 g hi) (h312 g hi)

theorem h333 : eval g w333 = 1 := by
  exact substitution_relation g 15 replacement16 w296 w333 false 0
    (by decide +kernel) (eq16 g hi) (h296 g hi)

theorem h336 : eval g w336 = 1 := by
  exact substitution_relation g 15 replacement16 w298 w336 false 0
    (by decide +kernel) (eq16 g hi) (h298 g hi)

theorem h337 : eval g w337 = 1 := by
  exact substitution_relation g 15 replacement16 w317 w337 false 0
    (by decide +kernel) (eq16 g hi) (h317 g hi)

theorem h338 : eval g w338 = 1 := by
  exact substitution_relation g 15 replacement16 w299 w338 false 0
    (by decide +kernel) (eq16 g hi) (h299 g hi)

theorem h343 : eval g w343 = 1 := by
  exact substitution_relation g 17 replacement18 w321 w343 false 0
    (by decide +kernel) (eq18 g hi) (h321 g hi)

theorem h344 : eval g w344 = 1 := by
  exact substitution_relation g 17 replacement18 w322 w344 false 0
    (by decide +kernel) (eq18 g hi) (h322 g hi)

theorem h345 : eval g w345 = 1 := by
  exact substitution_relation g 17 replacement18 w234 w345 false 0
    (by decide +kernel) (eq18 g hi) (h234 g hi)

theorem eq19 : g 18 = eval g replacement19 :=
  generator_equation g 18 replacement19 w345 true 5
    (by decide +kernel) (h345 g hi)

theorem h346 : eval g w346 = 1 := by
  exact substitution_relation g 17 replacement18 w323 w346 false 0
    (by decide +kernel) (eq18 g hi) (h323 g hi)

theorem h347 : eval g w347 = 1 := by
  exact substitution_relation g 17 replacement18 w305 w347 false 0
    (by decide +kernel) (eq18 g hi) (h305 g hi)

theorem h349 : eval g w349 = 1 := by
  exact substitution_relation g 17 replacement18 w325 w349 false 0
    (by decide +kernel) (eq18 g hi) (h325 g hi)

theorem h350 : eval g w350 = 1 := by
  exact substitution_relation g 17 replacement18 w326 w350 false 0
    (by decide +kernel) (eq18 g hi) (h326 g hi)

theorem h352 : eval g w352 = 1 := by
  exact substitution_relation g 17 replacement18 w329 w352 false 0
    (by decide +kernel) (eq18 g hi) (h329 g hi)

theorem h354 : eval g w354 = 1 := by
  exact substitution_relation g 17 replacement18 w333 w354 false 0
    (by decide +kernel) (eq18 g hi) (h333 g hi)

theorem h356 : eval g w356 = 1 := by
  exact substitution_relation g 17 replacement18 w338 w356 false 0
    (by decide +kernel) (eq18 g hi) (h338 g hi)

theorem h358 : eval g w358 = 1 := by
  exact substitution_relation g 17 replacement18 w256 w358 false 0
    (by decide +kernel) (eq18 g hi) (h256 g hi)

theorem h361 : eval g w361 = 1 := by
  exact substitution_relation g 19 replacement20 w343 w361 false 0
    (by decide +kernel) (eq20 g hi) (h343 g hi)

theorem h362 : eval g w362 = 1 := by
  exact substitution_relation g 19 replacement20 w344 w362 false 0
    (by decide +kernel) (eq20 g hi) (h344 g hi)

theorem h363 : eval g w363 = 1 := by
  exact substitution_relation g 19 replacement20 w346 w363 false 0
    (by decide +kernel) (eq20 g hi) (h346 g hi)

theorem h364 : eval g w364 = 1 := by
  exact substitution_relation g 19 replacement20 w347 w364 false 0
    (by decide +kernel) (eq20 g hi) (h347 g hi)

theorem h366 : eval g w366 = 1 := by
  exact substitution_relation g 19 replacement20 w307 w366 false 0
    (by decide +kernel) (eq20 g hi) (h307 g hi)

theorem h368 : eval g w368 = 1 := by
  exact substitution_relation g 19 replacement20 w350 w368 false 0
    (by decide +kernel) (eq20 g hi) (h350 g hi)

theorem h370 : eval g w370 = 1 := by
  exact substitution_relation g 19 replacement20 w352 w370 false 0
    (by decide +kernel) (eq20 g hi) (h352 g hi)

theorem h372 : eval g w372 = 1 := by
  exact substitution_relation g 19 replacement20 w314 w372 false 0
    (by decide +kernel) (eq20 g hi) (h314 g hi)

theorem h376 : eval g w376 = 1 := by
  exact substitution_relation g 19 replacement20 w278 w376 true 1
    (by decide +kernel) (eq20 g hi) (h278 g hi)

theorem eq9 : g 8 = eval g replacement9 :=
  generator_equation g 8 replacement9 w376 true 2
    (by decide +kernel) (h376 g hi)

theorem h377 : eval g w377 = 1 := by
  exact substitution_relation g 19 replacement20 w337 w377 false 0
    (by decide +kernel) (eq20 g hi) (h337 g hi)

theorem h380 : eval g w380 = 1 := by
  exact substitution_relation g 19 replacement20 w282 w380 false 0
    (by decide +kernel) (eq20 g hi) (h282 g hi)

theorem h383 : eval g w383 = 1 := by
  exact substitution_relation g 21 replacement22 w361 w383 false 0
    (by decide +kernel) (eq22 g hi) (h361 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
