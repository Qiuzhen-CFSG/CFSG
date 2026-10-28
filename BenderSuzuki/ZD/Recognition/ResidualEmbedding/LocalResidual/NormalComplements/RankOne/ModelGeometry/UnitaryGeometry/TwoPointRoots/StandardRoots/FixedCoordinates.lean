module

public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
import all Theory.SpecificGroups.SU3.ProjectiveGraphFixed

/-!
# Matrix equation for the graph-fixed SL₂ equivalence

Source: the fixed-field block calculation of GLS4, Chapter 4, Lemma 3.4(c),
used to identify the root-generated subgroup in Lemma 3.2(h).

The internal import is an equation interface for the existing opaque
`specialGraphFixedEquivSL2`. It is used only to prove its literal inverse
matrix formula, so consumers can use ordinary public imports.
-/

open Matrix
namespace BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
open BenderSuzuki.MatrixGroups BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

public theorem fixedEquiv_symm_val
    (A : Matrix.SpecialLinearGroup (Fin 2) (FixedBy.subfield E J.conj)) :
    ((specialGraphFixedEquivSL2 J hJ).symm A).val.val.val =
      !![(A 0 0 : E),0,(A 0 1 : E);0,1,0;(A 1 0 : E),0,(A 1 1 : E)] := by
  rfl

end BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
