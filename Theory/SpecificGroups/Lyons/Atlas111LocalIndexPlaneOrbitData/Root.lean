module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneOrbitData.Encoding

/-!
# The packed root of the Lyons plane tree

These seven integers are the base-eight encodings of the literal root columns
in `Atlas111LocalIndexPlane`. They are reproduced by
`Atlas111PlaneOrbitSource/GenerateOrbit.py`; the equality and reduced shape
below are checked by the Lean kernel. This module supplies only the root,
not a claim about the number of distinct translates.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitData
open Matrix

/-- Packed columns of the exact source plane. -/
def rootRows : PackedRows := ![8762105790959755756060130880744731750342084203788147883053792837648370205520044076542497082109329409, 2303129456068434989630645507190519128295365468183992434790018156789742632772528802366483268359946248, 6887235193021540694091738768129590880338331387739597503586298648948327397727074671649307670192586816, 1108805077513942600977000648833794841812002567115311822797893588025911457789014078026571908483383808, 9646868535874473965391824959272731057004644176080713705654346978576106464979826755393678481035366400, 1176680019138951833413652378468984592194692504686471277707455975171133786331759396541555193619185664, 5622653565331416805405069516920508797461503547338504001397581122664717021040791296325322009609502720]

/-- The root has pivots in the first seven rows. -/
def rootPivots : Fin 7 → Fin 111 := ![0, 1, 2, 3, 4, 5, 6]

set_option maxRecDepth 10000 in
/-- The integer encoding reconstructs the actual source matrix. -/
theorem root_columns : columns rootRows = separationPlaneColumns := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Every packed root column uses canonical GF(5) digits. -/
theorem root_validColumns : ∀ j, ValidColumn (rootRows j) := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- The root passes the executable reduced-shape check. -/
theorem root_checkReduced : checkReduced rootRows rootPivots = true := by
  decide +kernel

/-- A reduced-basis witness for the packed root. -/
def root_reduced : ReducedColumnBasis (columns rootRows) :=
  reducedBasisOfCheck root_checkReduced

/-- A reduced-basis witness for the source plane itself. -/
def separationPlaneColumns_reduced : ReducedColumnBasis separationPlaneColumns :=
  root_columns ▸ root_reduced

end Lyons.OrderCertificate.PlaneOrbitData
