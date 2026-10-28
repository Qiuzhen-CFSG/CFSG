module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry.Data

/-!
# Kernel checks for the Sylow involution colorings

Only evaluations on the three points 0, 1, 2 are needed as necessary conditions
for squaring to one or commuting. Noncentral inner involutions have no fixed
points, so a conjugate of the specified 2-central involution is covered by the
12-entry list. The final two checks certify the four- and eight-color bounds.
Source: Aschbacher--Smith K.4.5, printed p.460.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo.InvolutionGeometry.Certificate
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.SylowData

set_option maxRecDepth 100000 in
theorem pure_cover_check : ∀ i : Fin 128, squareKeys (sTable i) →
    pureIndex (pureDecode i) = i ∨ ∀ x, sTable i x ≠ x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem square_cover_check : ∀ i : Fin 256, squareKeys (table i) →
    candidate (decode i) = i := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem outer_cover_check : ∀ i : Fin 256, 128 ≤ i.val → squareKeys (table i) →
    candidate (outerIndex (outerDecode i)) = i := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem commute_check : ∀ i j : Fin 60,
    commuteKeys (table (candidate i)) (table (candidate j)) → adjacent i j = true := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem pure_color_check : ∀ i j : Fin 12,
    commuteKeys (sTable (pureIndex i)) (sTable (pureIndex j)) →
    pureColor i = pureColor j → i = j := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
theorem outer_color_check : ∀ (o : Fin 24) (i j : Fin 60),
    adjacent (outerIndex o) i = true → adjacent (outerIndex o) j = true →
    adjacent i j = true → outerColor o i = outerColor o j → i = j := by
  apply allFin
  decide +kernel

end CFSG.Quasithin.ChapterK.JankoTwo.InvolutionGeometry.Certificate
