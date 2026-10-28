module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationLow.ThreeB.Rows

/-!
# Matrix witnesses for normal generation by the second Thompson three-word

Writing `r = (ababab²)^6`, these products certify `(b*a*r*(a*b²)*a)^27 = 1`.
The original word products are reused from `ClassCoverage.Threes`; the new
packed products are checked in the kernel via `BinaryMatrix.decode_mul`.
Source matrices: ATLAS Th, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ .
See `Model/source/README.md` and `ThreeB/source/README.md` for provenance.
-/

@[expose] public section
namespace Thompson.Simplicity.ThreeBNormalCertificate
open ThreeWordCertificate
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
private theorem ba_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct atlasBRows[i.val]! atlasARows 248 = baRows[i.val]! := by
  decide +kernel

 theorem ba_product : BinaryMatrix.decode 248 atlasBRows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 baRows :=
  BinaryMatrix.decode_mul 248 atlasBRows atlasARows baRows ba_check

set_option maxHeartbeats 4000000 in
private theorem bar_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct baRows[i.val]! rBRows 248 = barRows[i.val]! := by
  decide +kernel

 theorem bar_product : BinaryMatrix.decode 248 baRows *
    BinaryMatrix.decode 248 rBRows = BinaryMatrix.decode 248 barRows :=
  BinaryMatrix.decode_mul 248 baRows rBRows barRows bar_check

set_option maxHeartbeats 4000000 in
private theorem barg_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct barRows[i.val]! ab2Rows 248 = bargRows[i.val]! := by
  decide +kernel

 theorem barg_product : BinaryMatrix.decode 248 barRows *
    BinaryMatrix.decode 248 ab2Rows = BinaryMatrix.decode 248 bargRows :=
  BinaryMatrix.decode_mul 248 barRows ab2Rows bargRows barg_check

set_option maxHeartbeats 4000000 in
private theorem t_check : ∀ i : Fin 248,
    BinaryMatrix.rowProduct bargRows[i.val]! atlasARows 248 = tRows[i.val]! := by
  decide +kernel

 theorem t_product : BinaryMatrix.decode 248 bargRows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 tRows :=
  BinaryMatrix.decode_mul 248 bargRows atlasARows tRows t_check

end Thompson.Simplicity.ThreeBNormalCertificate
