module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Rules

/-!
# Checked Tietze relations (block 0)

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

theorem h0 : eval g w0 = 1 := by
  exact normalized_relation g (inputWord 0) w0 true 0
    (by decide +kernel) (hi 0)

theorem eq1 : g 0 = eval g replacement1 :=
  generator_equation g 0 replacement1 w0 true 0
    (by decide +kernel) (h0 g hi)

theorem h1 : eval g w1 = 1 := by
  exact normalized_relation g (inputWord 1) w1 true 0
    (by decide +kernel) (hi 1)

theorem eq3 : g 2 = eval g replacement3 :=
  generator_equation g 2 replacement3 w1 true 0
    (by decide +kernel) (h1 g hi)

theorem h2 : eval g w2 = 1 := by
  exact normalized_relation g (inputWord 2) w2 true 9
    (by decide +kernel) (hi 2)

theorem h3 : eval g w3 = 1 := by
  exact normalized_relation g (inputWord 3) w3 false 12
    (by decide +kernel) (hi 3)

theorem h4 : eval g w4 = 1 := by
  exact normalized_relation g (inputWord 4) w4 false 9
    (by decide +kernel) (hi 4)

theorem h5 : eval g w5 = 1 := by
  exact normalized_relation g (inputWord 5) w5 true 9
    (by decide +kernel) (hi 5)

theorem h6 : eval g w6 = 1 := by
  exact normalized_relation g (inputWord 6) w6 true 12
    (by decide +kernel) (hi 6)

theorem h7 : eval g w7 = 1 := by
  exact normalized_relation g (inputWord 7) w7 true 1
    (by decide +kernel) (hi 7)

theorem eq23 : g 22 = eval g replacement23 :=
  generator_equation g 22 replacement23 w7 true 0
    (by decide +kernel) (h7 g hi)

theorem h8 : eval g w8 = 1 := by
  exact normalized_relation g (inputWord 8) w8 true 0
    (by decide +kernel) (hi 8)

theorem eq24 : g 23 = eval g replacement24 :=
  generator_equation g 23 replacement24 w8 true 0
    (by decide +kernel) (h8 g hi)

theorem h9 : eval g w9 = 1 := by
  exact normalized_relation g (inputWord 11) w9 false 23
    (by decide +kernel) (hi 11)

theorem h11 : eval g w11 = 1 := by
  exact normalized_relation g (inputWord 13) w11 false 0
    (by decide +kernel) (hi 13)

theorem h12 : eval g w12 = 1 := by
  exact normalized_relation g (inputWord 14) w12 true 0
    (by decide +kernel) (hi 14)

theorem eq18 : g 17 = eval g replacement18 :=
  generator_equation g 17 replacement18 w12 true 0
    (by decide +kernel) (h12 g hi)

theorem h13 : eval g w13 = 1 := by
  exact normalized_relation g (inputWord 15) w13 true 0
    (by decide +kernel) (hi 15)

theorem eq14 : g 13 = eval g replacement14 :=
  generator_equation g 13 replacement14 w13 true 0
    (by decide +kernel) (h13 g hi)

theorem h16 : eval g w16 = 1 := by
  exact normalized_relation g (inputWord 19) w16 true 1
    (by decide +kernel) (hi 19)

theorem h17 : eval g w17 = 1 := by
  exact normalized_relation g (inputWord 20) w17 true 8
    (by decide +kernel) (hi 20)

theorem h18 : eval g w18 = 1 := by
  exact normalized_relation g (inputWord 21) w18 true 0
    (by decide +kernel) (hi 21)

theorem eq13 : g 12 = eval g replacement13 :=
  generator_equation g 12 replacement13 w18 true 0
    (by decide +kernel) (h18 g hi)

theorem h19 : eval g w19 = 1 := by
  exact normalized_relation g (inputWord 22) w19 true 0
    (by decide +kernel) (hi 22)

theorem eq15 : g 14 = eval g replacement15 :=
  generator_equation g 14 replacement15 w19 true 0
    (by decide +kernel) (h19 g hi)

theorem h22 : eval g w22 = 1 := by
  exact normalized_relation g (inputWord 27) w22 true 20
    (by decide +kernel) (hi 27)

theorem h23 : eval g w23 = 1 := by
  exact normalized_relation g (inputWord 30) w23 true 0
    (by decide +kernel) (hi 30)

theorem h25 : eval g w25 = 1 := by
  exact normalized_relation g (inputWord 35) w25 true 0
    (by decide +kernel) (hi 35)

theorem eq10 : g 9 = eval g replacement10 :=
  generator_equation g 9 replacement10 w25 true 0
    (by decide +kernel) (h25 g hi)

theorem h26 : eval g w26 = 1 := by
  exact normalized_relation g (inputWord 36) w26 true 0
    (by decide +kernel) (hi 36)

theorem eq7 : g 6 = eval g replacement7 :=
  generator_equation g 6 replacement7 w26 true 0
    (by decide +kernel) (h26 g hi)

theorem h27 : eval g w27 = 1 := by
  exact normalized_relation g (inputWord 40) w27 true 3
    (by decide +kernel) (hi 40)

theorem h28 : eval g w28 = 1 := by
  exact normalized_relation g (inputWord 42) w28 true 0
    (by decide +kernel) (hi 42)

theorem eq22 : g 21 = eval g replacement22 :=
  generator_equation g 21 replacement22 w28 true 0
    (by decide +kernel) (h28 g hi)

theorem h32 : eval g w32 = 1 := by
  exact normalized_relation g (inputWord 55) w32 true 5
    (by decide +kernel) (hi 55)

theorem h33 : eval g w33 = 1 := by
  exact normalized_relation g (inputWord 56) w33 true 0
    (by decide +kernel) (hi 56)

theorem eq20 : g 19 = eval g replacement20 :=
  generator_equation g 19 replacement20 w33 true 0
    (by decide +kernel) (h33 g hi)

theorem h34 : eval g w34 = 1 := by
  exact normalized_relation g (inputWord 57) w34 true 0
    (by decide +kernel) (hi 57)

theorem h37 : eval g w37 = 1 := by
  exact normalized_relation g (inputWord 70) w37 true 0
    (by decide +kernel) (hi 70)

theorem eq4 : g 3 = eval g replacement4 :=
  generator_equation g 3 replacement4 w37 true 0
    (by decide +kernel) (h37 g hi)

theorem h38 : eval g w38 = 1 := by
  exact normalized_relation g (inputWord 75) w38 true 6
    (by decide +kernel) (hi 75)

theorem h39 : eval g w39 = 1 := by
  exact normalized_relation g (inputWord 77) w39 true 0
    (by decide +kernel) (hi 77)

theorem eq8 : g 7 = eval g replacement8 :=
  generator_equation g 7 replacement8 w39 true 0
    (by decide +kernel) (h39 g hi)

theorem h41 : eval g w41 = 1 := by
  exact normalized_relation g (inputWord 82) w41 false 0
    (by decide +kernel) (hi 82)

theorem h42 : eval g w42 = 1 := by
  exact normalized_relation g (inputWord 84) w42 true 0
    (by decide +kernel) (hi 84)

theorem eq16 : g 15 = eval g replacement16 :=
  generator_equation g 15 replacement16 w42 true 0
    (by decide +kernel) (h42 g hi)

theorem h43 : eval g w43 = 1 := by
  exact normalized_relation g (inputWord 85) w43 true 0
    (by decide +kernel) (hi 85)

theorem h44 : eval g w44 = 1 := by
  exact normalized_relation g (inputWord 88) w44 false 3
    (by decide +kernel) (hi 88)

theorem h45 : eval g w45 = 1 := by
  exact normalized_relation g (inputWord 89) w45 true 9
    (by decide +kernel) (hi 89)

theorem h46 : eval g w46 = 1 := by
  exact normalized_relation g (inputWord 90) w46 false 3
    (by decide +kernel) (hi 90)

theorem h47 : eval g w47 = 1 := by
  exact normalized_relation g (inputWord 92) w47 true 0
    (by decide +kernel) (hi 92)

theorem eq11 : g 10 = eval g replacement11 :=
  generator_equation g 10 replacement11 w47 true 0
    (by decide +kernel) (h47 g hi)

theorem h49 : eval g w49 = 1 := by
  exact normalized_relation g (inputWord 98) w49 true 0
    (by decide +kernel) (hi 98)

theorem eq12 : g 11 = eval g replacement12 :=
  generator_equation g 11 replacement12 w49 true 0
    (by decide +kernel) (h49 g hi)

theorem h52 : eval g w52 = 1 := by
  exact normalized_relation g (inputWord 111) w52 true 1
    (by decide +kernel) (hi 111)

theorem h54 : eval g w54 = 1 := by
  exact normalized_relation g (inputWord 118) w54 true 2
    (by decide +kernel) (hi 118)

theorem h62 : eval g w62 = 1 := by
  exact normalized_relation g (inputWord 154) w62 true 0
    (by decide +kernel) (hi 154)

theorem eq5 : g 4 = eval g replacement5 :=
  generator_equation g 4 replacement5 w62 true 0
    (by decide +kernel) (h62 g hi)

theorem h63 : eval g w63 = 1 := by
  exact normalized_relation g (inputWord 155) w63 true 0
    (by decide +kernel) (hi 155)

theorem h64 : eval g w64 = 1 := by
  exact normalized_relation g (inputWord 158) w64 true 3
    (by decide +kernel) (hi 158)

theorem h68 : eval g w68 = 1 := by
  exact substitution_relation g 0 replacement1 w2 w68 false 0
    (by decide +kernel) (eq1 g hi) (h2 g hi)

theorem h69 : eval g w69 = 1 := by
  exact substitution_relation g 0 replacement1 w4 w69 false 0
    (by decide +kernel) (eq1 g hi) (h4 g hi)

theorem h70 : eval g w70 = 1 := by
  exact substitution_relation g 0 replacement1 w5 w70 false 0
    (by decide +kernel) (eq1 g hi) (h5 g hi)

theorem h71 : eval g w71 = 1 := by
  exact substitution_relation g 0 replacement1 w6 w71 false 0
    (by decide +kernel) (eq1 g hi) (h6 g hi)

theorem h72 : eval g w72 = 1 := by
  exact substitution_relation g 0 replacement1 w11 w72 false 0
    (by decide +kernel) (eq1 g hi) (h11 g hi)

theorem h74 : eval g w74 = 1 := by
  exact substitution_relation g 0 replacement1 w16 w74 false 0
    (by decide +kernel) (eq1 g hi) (h16 g hi)

theorem h77 : eval g w77 = 1 := by
  exact substitution_relation g 0 replacement1 w32 w77 false 0
    (by decide +kernel) (eq1 g hi) (h32 g hi)

theorem h78 : eval g w78 = 1 := by
  exact substitution_relation g 0 replacement1 w38 w78 false 0
    (by decide +kernel) (eq1 g hi) (h38 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
