module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound.ComparisonGeneration.EliminationData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Rules

/-!
# Relative elimination for the eight fixed comparison words

The eight new letters denote exactly `Comparison.generatorWord`. Elementary
Tietze equations recover twenty original letters from those eight and original
letters 2, 7, 10, 17 (zero based). This is a relative generation reduction;
no membership of the four survivors is assumed by the replay itself.
Source: the literal ATLAS M24G1-P1 Schreier presentation. See `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison.Elimination
open Subgroup.CosetWordCertificate
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction

variable {G : Type*} [Group G] (g : Nat → G)
  (hi : ∀ r : Fin 445, eval g (inputWord r) = 1)
include hi

theorem h1 : eval g w1 = 1 := by
  exact normalized_relation g (inputWord 1) w1 false 0
    (by decide +kernel) (hi 1)

theorem eq1 : g 0 = eval g replacement1 :=
  generator_equation g 0 replacement1 w1 true 0
    (by decide +kernel) (h1 g hi)

theorem h23 : eval g w23 = 1 := by
  exact normalized_relation g (inputWord 26) w23 false 5
    (by decide +kernel) (hi 26)

theorem h37 : eval g w37 = 1 := by
  exact normalized_relation g (inputWord 42) w37 true 3
    (by decide +kernel) (hi 42)

theorem h39 : eval g w39 = 1 := by
  exact normalized_relation g (inputWord 45) w39 true 8
    (by decide +kernel) (hi 45)

theorem h50 : eval g w50 = 1 := by
  exact normalized_relation g (inputWord 58) w50 false 0
    (by decide +kernel) (hi 58)

theorem eq7 : g 6 = eval g replacement7 :=
  generator_equation g 6 replacement7 w50 true 0
    (by decide +kernel) (h50 g hi)

theorem h51 : eval g w51 = 1 := by
  exact normalized_relation g (inputWord 59) w51 false 3
    (by decide +kernel) (hi 59)

theorem eq15 : g 14 = eval g replacement15 :=
  generator_equation g 14 replacement15 w51 true 1
    (by decide +kernel) (h51 g hi)

theorem h83 : eval g w83 = 1 := by
  exact normalized_relation g (inputWord 96) w83 false 1
    (by decide +kernel) (hi 96)

theorem eq10 : g 9 = eval g replacement10 :=
  generator_equation g 9 replacement10 w83 true 0
    (by decide +kernel) (h83 g hi)

theorem h116 : eval g w116 = 1 := by
  exact normalized_relation g (inputWord 134) w116 false 0
    (by decide +kernel) (hi 134)

theorem eq6 : g 5 = eval g replacement6 :=
  generator_equation g 5 replacement6 w116 true 1
    (by decide +kernel) (h116 g hi)

theorem h129 : eval g w129 = 1 := by
  exact normalized_relation g (inputWord 149) w129 true 1
    (by decide +kernel) (hi 149)

theorem h132 : eval g w132 = 1 := by
  exact normalized_relation g (inputWord 154) w132 false 4
    (by decide +kernel) (hi 154)

theorem h163 : eval g w163 = 1 := by
  exact normalized_relation g (inputWord 197) w163 true 3
    (by decide +kernel) (hi 197)

theorem h188 : eval g w188 = 1 := by
  exact normalized_relation g (inputWord 229) w188 false 0
    (by decide +kernel) (hi 229)

theorem eq17 : g 16 = eval g replacement17 :=
  generator_equation g 16 replacement17 w188 true 0
    (by decide +kernel) (h188 g hi)

theorem h233 : eval g w233 = 1 := by
  exact normalized_relation g (inputWord 289) w233 true 8
    (by decide +kernel) (hi 289)

theorem h251 : eval g w251 = 1 := by
  exact normalized_relation g (inputWord 311) w251 false 0
    (by decide +kernel) (hi 311)

theorem h260 : eval g w260 = 1 := by
  exact normalized_relation g (inputWord 324) w260 false 0
    (by decide +kernel) (hi 324)

theorem eq22 : g 21 = eval g replacement22 :=
  generator_equation g 21 replacement22 w260 true 1
    (by decide +kernel) (h260 g hi)

theorem h272 : eval g w272 = 1 := by
  exact normalized_relation g (inputWord 339) w272 false 2
    (by decide +kernel) (hi 339)

theorem h339 : eval g w339 = 1 := by
  exact normalized_relation g (inputWord 437) w339 false 0
    (by decide +kernel) (hi 437)

theorem h340 : eval g w340 = 1 := by
  exact normalized_relation g (inputWord 438) w340 false 0
    (by decide +kernel) (hi 438)

theorem eq2 : g 1 = eval g replacement2 :=
  generator_equation g 1 replacement2 w340 true 2
    (by decide +kernel) (h340 g hi)

theorem h343 : eval g w343 = 1 := by
  exact normalized_relation g (inputWord 441) w343 false 0
    (by decide +kernel) (hi 441)

theorem h346 : eval g w346 = 1 := by
  exact normalized_relation g (inputWord 444) w346 false 0
    (by decide +kernel) (hi 444)

theorem eq19 : g 18 = eval g replacement19 :=
  generator_equation g 18 replacement19 w346 true 2
    (by decide +kernel) (h346 g hi)

theorem h367 : eval g w367 = 1 := by
  exact substitution_relation g 0 replacement1 w37 w367 false 0
    (by decide +kernel) (eq1 g hi) (h37 g hi)

theorem h368 : eval g w368 = 1 := by
  exact substitution_relation g 0 replacement1 w39 w368 false 0
    (by decide +kernel) (eq1 g hi) (h39 g hi)

theorem h409 : eval g w409 = 1 := by
  exact substitution_relation g 0 replacement1 w129 w409 false 0
    (by decide +kernel) (eq1 g hi) (h129 g hi)

theorem h451 : eval g w451 = 1 := by
  exact substitution_relation g 0 replacement1 w233 w451 false 0
    (by decide +kernel) (eq1 g hi) (h233 g hi)

theorem h469 : eval g w469 = 1 := by
  exact substitution_relation g 0 replacement1 w272 w469 false 0
    (by decide +kernel) (eq1 g hi) (h272 g hi)

theorem eq4 : g 3 = eval g replacement4 :=
  generator_equation g 3 replacement4 w469 false 1
    (by decide +kernel) (h469 g hi)

theorem h511 : eval g w511 = 1 := by
  exact substitution_relation g 6 replacement7 w368 w511 false 0
    (by decide +kernel) (eq7 g hi) (h368 g hi)

theorem h558 : eval g w558 = 1 := by
  exact substitution_relation g 6 replacement7 w163 w558 false 0
    (by decide +kernel) (eq7 g hi) (h163 g hi)

theorem h591 : eval g w591 = 1 := by
  exact substitution_relation g 6 replacement7 w451 w591 false 0
    (by decide +kernel) (eq7 g hi) (h451 g hi)

theorem h681 : eval g w681 = 1 := by
  exact substitution_relation g 16 replacement17 w132 w681 false 0
    (by decide +kernel) (eq17 g hi) (h132 g hi)

theorem h824 : eval g w824 = 1 := by
  exact substitution_relation g 5 replacement6 w681 w824 false 0
    (by decide +kernel) (eq6 g hi) (h681 g hi)

theorem eq20 : g 19 = eval g replacement20 :=
  generator_equation g 19 replacement20 w824 true 7
    (by decide +kernel) (h824 g hi)

theorem h835 : eval g w835 = 1 := by
  exact substitution_relation g 5 replacement6 w558 w835 false 0
    (by decide +kernel) (eq6 g hi) (h558 g hi)

theorem h923 : eval g w923 = 1 := by
  exact substitution_relation g 9 replacement10 w511 w923 false 0
    (by decide +kernel) (eq10 g hi) (h511 g hi)

theorem h1012 : eval g w1012 = 1 := by
  exact substitution_relation g 9 replacement10 w251 w1012 false 0
    (by decide +kernel) (eq10 g hi) (h251 g hi)

theorem eq14 : g 13 = eval g replacement14 :=
  generator_equation g 13 replacement14 w1012 false 5
    (by decide +kernel) (h1012 g hi)

theorem h1041 : eval g w1041 = 1 := by
  exact substitution_relation g 9 replacement10 w339 w1041 false 0
    (by decide +kernel) (eq10 g hi) (h339 g hi)

theorem eq5 : g 4 = eval g replacement5 :=
  generator_equation g 4 replacement5 w1041 true 0
    (by decide +kernel) (h1041 g hi)

theorem h1043 : eval g w1043 = 1 := by
  exact substitution_relation g 9 replacement10 w343 w1043 false 0
    (by decide +kernel) (eq10 g hi) (h343 g hi)

theorem eq13 : g 12 = eval g replacement13 :=
  generator_equation g 12 replacement13 w1043 true 0
    (by decide +kernel) (h1043 g hi)

theorem h1352 : eval g w1352 = 1 := by
  exact substitution_relation g 3 replacement4 w367 w1352 false 2
    (by decide +kernel) (eq4 g hi) (h367 g hi)

theorem h1495 : eval g w1495 = 1 := by
  exact substitution_relation g 12 replacement13 w923 w1495 false 7
    (by decide +kernel) (eq13 g hi) (h923 g hi)

theorem h1524 : eval g w1524 = 1 := by
  exact substitution_relation g 12 replacement13 w409 w1524 false 2
    (by decide +kernel) (eq13 g hi) (h409 g hi)

theorem eq21 : g 20 = eval g replacement21 :=
  generator_equation g 20 replacement21 w1524 true 1
    (by decide +kernel) (h1524 g hi)

theorem h1559 : eval g w1559 = 1 := by
  exact substitution_relation g 12 replacement13 w591 w1559 false 4
    (by decide +kernel) (eq13 g hi) (h591 g hi)

theorem h1625 : eval g w1625 = 1 := by
  exact substitution_relation g 13 replacement14 w23 w1625 false 0
    (by decide +kernel) (eq14 g hi) (h23 g hi)

theorem eq23 : g 22 = eval g replacement23 :=
  generator_equation g 22 replacement23 w1625 false 1
    (by decide +kernel) (h1625 g hi)

theorem h1851 : eval g w1851 = 1 := by
  exact substitution_relation g 19 replacement20 w1559 w1851 false 0
    (by decide +kernel) (eq20 g hi) (h1559 g hi)

theorem h2191 : eval g w2191 = 1 := by
  exact substitution_relation g 4 replacement5 w1495 w2191 false 0
    (by decide +kernel) (eq5 g hi) (h1495 g hi)

theorem eq16 : g 15 = eval g replacement16 :=
  generator_equation g 15 replacement16 w2191 true 7
    (by decide +kernel) (h2191 g hi)

theorem h2285 : eval g w2285 = 1 := by
  exact substitution_relation g 4 replacement5 w835 w2285 true 6
    (by decide +kernel) (eq5 g hi) (h835 g hi)

theorem eq12 : g 11 = eval g replacement12 :=
  generator_equation g 11 replacement12 w2285 true 5
    (by decide +kernel) (h2285 g hi)

theorem h2341 : eval g w2341 = 1 := by
  exact substitution_relation g 4 replacement5 w1851 w2341 false 0
    (by decide +kernel) (eq5 g hi) (h1851 g hi)

theorem h2454 : eval g w2454 = 1 := by
  exact substitution_relation g 18 replacement19 w1352 w2454 false 3
    (by decide +kernel) (eq19 g hi) (h1352 g hi)

theorem eq24 : g 23 = eval g replacement24 :=
  generator_equation g 23 replacement24 w2454 true 2
    (by decide +kernel) (h2454 g hi)

theorem h2613 : eval g w2613 = 1 := by
  exact substitution_relation g 18 replacement19 w2341 w2613 false 19
    (by decide +kernel) (eq19 g hi) (h2341 g hi)

theorem h3420 : eval g w3420 = 1 := by
  exact substitution_relation g 11 replacement12 w2613 w3420 false 0
    (by decide +kernel) (eq12 g hi) (h2613 g hi)

theorem h3725 : eval g w3725 = 1 := by
  exact substitution_relation g 20 replacement21 w3420 w3725 false 0
    (by decide +kernel) (eq21 g hi) (h3420 g hi)

theorem h4043 : eval g w4043 = 1 := by
  exact substitution_relation g 15 replacement16 w3725 w4043 false 0
    (by decide +kernel) (eq16 g hi) (h3725 g hi)

theorem eq9 : g 8 = eval g replacement9 :=
  generator_equation g 8 replacement9 w4043 false 9
    (by decide +kernel) (h4043 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison.Elimination
