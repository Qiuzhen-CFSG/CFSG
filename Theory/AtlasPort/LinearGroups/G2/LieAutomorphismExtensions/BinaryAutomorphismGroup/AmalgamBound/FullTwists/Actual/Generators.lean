module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.FullTwists.Actual.Coordinates

/-!
# Small coordinate formulas for the full binary G₂ generators

The original root and Weyl maps act by these explicit binary linear formulas.
Proving the formulas once keeps the table certificates from repeatedly
reducing compositions of root equivalences. They are consumed by `Checks`.

Source: Aschbacher--Smith F.1.12(I)(3), q = 2, pp.262--263. Coordinates follow
Gerald Höhn and the ATLAS contributors, ATLAS Research and Attribution
License 1.0 (`LICENSES/ATLAS.txt`).
-/

@[expose] public section
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Explicit
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual
def commonApply (x : Carrier (ZMod 2)) : Carrier (ZMod 2) :=
  ![x 0 + x 1 + x 3 + x 4 + x 7, x 1 + x 2 + x 3 + x 4 + x 6 + x 7, x 2 + x 3 + x 4 + x 5 + x 6 + x 7, x 3 + x 5 + x 7, x 4 + x 5 + x 7, x 5 + x 6 + x 7, x 6 + x 7, x 7]

def leftApply (x : Carrier (ZMod 2)) : Carrier (ZMod 2) :=
  ![x 0 + x 1, x 0, x 2 + x 3 + x 4 + x 5, x 2 + x 4, x 2 + x 3, x 2, x 6 + x 7, x 6]

def rightApply (x : Carrier (ZMod 2)) : Carrier (ZMod 2) :=
  ![x 0, x 1 + x 2, x 1, x 3, x 4, x 5 + x 6, x 5, x 7]

def thirdApply (x : Carrier (ZMod 2)) : Carrier (ZMod 2) :=
  ![x 0 + x 3 + x 4 + x 7, x 1 + x 5, x 2 + x 6, x 3 + x 7, x 4 + x 7, x 5, x 6, x 7]

theorem common_apply (x : Carrier (ZMod 2)) : commonGenerator.val x = commonApply x := by
  change rootCApply 1 (rootEApply 1 (rootFApply 1 x)) = _
  ext i
  fin_cases i <;> simp [rootCApply, rootEApply, rootFApply, commonApply,
    sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 by decide]

theorem left_apply (x : Carrier (ZMod 2)) :
    (rootF 1 * weylS : Model (ZMod 2)).val x = leftApply x := by
  change rootFApply 1 (weylSApply x) = _
  ext i
  fin_cases i <;> simp [rootFApply, weylSApply, leftApply,
    sub_eq_add_neg, CharTwo.neg_eq] <;> ring

theorem right_apply (x : Carrier (ZMod 2)) :
    (rootE 1 * weylR : Model (ZMod 2)).val x = rightApply x := by
  change rootEApply 1 (weylRApply x) = _
  ext i
  fin_cases i <;> simp [rootEApply, weylRApply, rightApply,
    sub_eq_add_neg, CharTwo.neg_eq] <;> ring

theorem third_apply (x : Carrier (ZMod 2)) :
    (rootC 1 : Model (ZMod 2)).val x = thirdApply x := by
  change rootCApply 1 x = _
  ext i
  fin_cases i <;> simp [rootCApply, thirdApply, sub_eq_add_neg, CharTwo.neg_eq]

def leftApplyGenerator : Fin 3 → Carrier (ZMod 2) → Carrier (ZMod 2) :=
  ![commonApply, leftApply, thirdApply]
def rightApplyGenerator : Fin 3 → Carrier (ZMod 2) → Carrier (ZMod 2) :=
  ![commonApply, rightApply, thirdApply]

theorem leftGenerators_apply (b : Fin 3) (x : Carrier (ZMod 2)) :
    (leftGenerators b).val x = leftApplyGenerator b x := by
  fin_cases b
  · exact common_apply x
  · exact left_apply x
  · exact third_apply x

theorem rightGenerators_apply (b : Fin 3) (x : Carrier (ZMod 2)) :
    (rightGenerators b).val x = rightApplyGenerator b x := by
  fin_cases b
  · exact common_apply x
  · exact right_apply x
  · exact third_apply x
end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.FullTwists.Actual
