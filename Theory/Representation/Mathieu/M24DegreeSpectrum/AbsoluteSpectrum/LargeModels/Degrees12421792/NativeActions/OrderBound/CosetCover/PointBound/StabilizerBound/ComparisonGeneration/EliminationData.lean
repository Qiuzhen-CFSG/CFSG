module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.StabilizerBound.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.WordLiteral

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

def inputWord (r : Fin 445) : Word Nat :=
  if h : r.val < 437 then
    (relatorLetters (⟨r.val / 19, by omega⟩, ⟨r.val % 19, by omega⟩)).map
      (fun a => (a.1.val, a.2))
  else
    [(r.val - 437 + 24, false)] ++
      (generatorWord ⟨r.val - 437, by omega⟩).map (fun a => (a.1.val, a.2))

def w1 : Word Nat := point_word% "-1"

def w23 : Word Nat := point_word% "-24,23,-9,-14,9,18,12"

def w37 : Word Nat := point_word% "-23,-1,-4,3,8,19,11,16"

def w39 : Word Nat := point_word% "-16,10,3,8,-1,3,8,-5,13,-1,3,7"

def w50 : Word Nat := point_word% "-7"

def w51 : Word Nat := point_word% "-21,3,19,-15,-18"

def w83 : Word Nat := point_word% "-11,-10"

def w116 : Word Nat := point_word% "-6,-5"

def w129 : Word Nat := point_word% "-21,8,13,-1,3,8,-18"

def w132 : Word Nat := point_word% "-20,-19,-17,18,-6,-8,-3,-16,-11"

def w163 : Word Nat := point_word% "-21,3,8,6,-18,-21,11,16,-7,8,12"

def w188 : Word Nat := point_word% "-17"

def w233 : Word Nat := point_word% "-21,-20,3,8,13,-1,3,7,9,21,-12,-18"

def w251 : Word Nat := point_word% "-16,9,-10,3,-9,14"

def w260 : Word Nat := point_word% "-23,-22,-15"

def w272 : Word Nat := point_word% "-24,-1,4,1,23,18,12"

def w339 : Word Nat := point_word% "-25,-8,10,8,-5"

def w340 : Word Nat := point_word% "-26,-15,-2,-21,-19"

def w343 : Word Nat := point_word% "-29,10,8,-10,-13"

def w346 : Word Nat := point_word% "-32,-18,-19,-8,18"

def w367 : Word Nat := point_word% "-23,-4,3,8,19,11,16"

def w368 : Word Nat := point_word% "-16,10,3,8,3,8,-5,13,3,7"

def w409 : Word Nat := point_word% "-21,8,13,3,8,-18"

def w451 : Word Nat := point_word% "-21,-20,3,8,13,3,7,9,21,-12,-18"

def w469 : Word Nat := point_word% "-24,4,23,18,12"

def w511 : Word Nat := point_word% "-16,10,3,8,3,8,-5,13,3"

def w558 : Word Nat := point_word% "-21,3,8,6,-18,-21,11,16,8,12"

def w591 : Word Nat := point_word% "-21,-20,3,8,13,3,9,21,-12,-18"

def w681 : Word Nat := point_word% "-20,-19,18,-6,-8,-3,-16,-11"

def w824 : Word Nat := point_word% "-20,-19,18,5,-8,-3,-16,-11"

def w835 : Word Nat := point_word% "-21,3,8,-5,-18,-21,11,16,8,12"

def w923 : Word Nat := point_word% "-16,-11,3,8,3,8,-5,13,3"

def w1012 : Word Nat := point_word% "-16,9,11,3,-9,14"

def w1041 : Word Nat := point_word% "-25,-8,-11,8,-5"

def w1043 : Word Nat := point_word% "-29,-11,8,11,-13"

def w1352 : Word Nat := point_word% "-24,3,8,19,11,16,18,12"

def w1495 : Word Nat := point_word% "-29,-11,8,11,3,-16,-11,3,8,3,8,-5"

def w1524 : Word Nat := point_word% "-29,-11,8,11,3,8,-18,-21,8"

def w1559 : Word Nat := point_word% "-29,-11,8,11,3,9,21,-12,-18,-21,-20,3,8"

def w1625 : Word Nat := point_word% "-24,23,-9,-16,9,11,3,18,12"

def w1851 : Word Nat := point_word% "-29,-11,8,11,3,9,21,-12,-18,-21,11,16,3,8,-5,-18,19,3,8"

def w2191 : Word Nat := point_word% "-29,-11,8,11,3,-16,-11,3,8,3,11,8,25"

def w2285 : Word Nat := point_word% "-25,-8,-11,-3,21,-12,-8,-16,-11,21,18"

def w2341 : Word Nat := point_word% "-29,-11,8,11,3,9,21,-12,-18,-21,11,16,3,11,8,25,-18,19,3,8"

def w2454 : Word Nat := point_word% "-32,-18,11,16,18,12,-24,3,18"

def w2613 : Word Nat := point_word% "-32,-18,3,8,-29,-11,8,11,3,9,21,-12,-18,-21,11,16,3,11,8,25,-18,-8,18"

def w3420 : Word Nat := point_word% "-32,-18,3,8,-29,-11,8,11,3,9,3,11,8,25,-18,-21,11,16,8,-18,-21,11,16,3,11,8,25,-18,-8,18"

def w3725 : Word Nat := point_word% "-32,-18,3,8,-29,-11,8,11,3,9,3,11,8,25,-8,-3,-11,-8,11,29,-8,11,16,-3,-11,-8,11,29,-8,11,16,3,11,8,25,-18,-8,18"

def w4043 : Word Nat := point_word% "-32,-18,3,8,-29,-11,8,11,3,9,3,11,8,25,-8,-3,-11,-8,11,29,-8,3,8,3,11,8,25,-8,3,8,3,11,8,25,-29,-11,8,11,3,3,11,8,25,-18,-8,18"

def replacement1 : Word Nat := point_word% ""

def replacement7 : Word Nat := point_word% ""

def replacement17 : Word Nat := point_word% ""

def replacement6 : Word Nat := point_word% "-5"

def replacement10 : Word Nat := point_word% "-11"

def replacement22 : Word Nat := point_word% "-15,-23"

def replacement2 : Word Nat := point_word% "-21,-19,-26,-15"

def replacement4 : Word Nat := point_word% "24,-12,-18,-23"

def replacement13 : Word Nat := point_word% "-29,-11,8,11"

def replacement14 : Word Nat := point_word% "9,-3,-11,-9,16"

def replacement20 : Word Nat := point_word% "-19,18,5,-8,-3,-16,-11"

def replacement15 : Word Nat := point_word% "-18,-21,3,19"

def replacement5 : Word Nat := point_word% "-25,-8,-11,8"

def replacement19 : Word Nat := point_word% "-8,18,-32,-18"

def replacement23 : Word Nat := point_word% "24,-12,-18,-3,-11,-9,16,9"

def replacement24 : Word Nat := point_word% "3,18,-32,-18,11,16,18,12"

def replacement12 : Word Nat := point_word% "-8,-16,-11,21,18,-25,-8,-11,-3,21"

def replacement21 : Word Nat := point_word% "8,-29,-11,8,11,3,8,-18"

def replacement16 : Word Nat := point_word% "-11,3,8,3,11,8,25,-29,-11,8,11,3"

def replacement9 : Word Nat := point_word% "-3,-11,-8,11,29,-8,-3,18,32,-18,8,18,-25,-8,-11,-3,-3,-11,-8,11,29,-25,-8,-11,-3,-8,-3,8,-25,-8,-11,-3,-8,-3,8,-29,-11,8,11,3,8,-25,-8,-11,-3"

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Stabilizer.Comparison.Elimination
