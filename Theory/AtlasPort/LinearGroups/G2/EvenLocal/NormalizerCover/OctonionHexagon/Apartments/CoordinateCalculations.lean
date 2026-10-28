module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The coordinate reductions use the root formulas of
Atlas/LinearGroups/G2/RootLinearMaps.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: calculate the annihilators and root reductions needed for intrinsic
hexagon normalization, preserving the actual octonion automorphism model.
-/

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.Configurations

/-!
# Coordinate calculations for octonion path normalization

The annihilators of basis vectors 0, 1, 5, and 7 are computed directly. Once
the first two points are normalized, root B followed by root C normalizes
the third point. Root D followed by root A then normalizes the fourth while
fixing the first three. Root E fixes this entire prefix.

The nonzero denominators are explicit hypotheses here. The geometric
normalization proofs must derive them from distinct incident lines.

Source context: the split G₂ geometry for Aschbacher--Smith, Theorem 0.1.2(1),
printed pp.3--4, and Theorem 0.1.1, printed pp.481--482.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
variable {F : Type*} [Field F]

theorem annihilator_basis_zero (x : Carrier F)
    (h : mul (basisVector 0) x = 0 ∧ mul x (basisVector 0) = 0) :
    x = ![x 0,x 1,x 2,0,0,0,0,0] := by
  have h3 : x 3 = 0 := by simpa [mul,basisVector] using congrFun h.2 0
  have h4 : x 4 = 0 := by simpa [mul,basisVector] using congrFun h.1 0
  have h5 : x 5 = 0 := by simpa [mul,basisVector] using congrFun h.1 1
  have h6 : x 6 = 0 := by simpa [mul,basisVector] using congrFun h.1 2
  have h7 : x 7 = 0 := by simpa [mul,basisVector] using congrFun h.1 3
  ext i
  fin_cases i <;> simp [h3,h4,h5,h6,h7]

theorem annihilator_basis_one (x : Carrier F)
    (h : mul (basisVector 1) x = 0 ∧ mul x (basisVector 1) = 0) :
    x = ![x 0,x 1,0,0,0,x 5,0,0] := by
  have h2 : x 2 = 0 := by simpa [mul,basisVector] using congrFun h.1 0
  have h3 : x 3 = 0 := by simpa [mul,basisVector] using congrFun h.1 1
  have h4 : x 4 = 0 := by simpa [mul,basisVector] using congrFun h.2 1
  have h6 : x 6 = 0 := by simpa [mul,basisVector] using congrFun h.1 4
  have h7 : x 7 = 0 := by simpa [mul,basisVector] using congrFun h.1 5
  ext i
  fin_cases i <;> simp [h2,h3,h4,h6,h7]

theorem annihilator_basis_five (x : Carrier F)
    (h : mul (basisVector 5) x = 0 ∧ mul x (basisVector 5) = 0) :
    x = ![0,x 1,0,0,0,x 5,0,x 7] := by
  have h0 : x 0 = 0 := by simpa [mul,basisVector] using congrFun h.1 1
  have h2 : x 2 = 0 := by simpa [mul,basisVector] using congrFun h.1 3
  have h3 : x 3 = 0 := by simpa [mul,basisVector] using congrFun h.2 5
  have h4 : x 4 = 0 := by simpa [mul,basisVector] using congrFun h.1 5
  have h6 : x 6 = 0 := by simpa [mul,basisVector] using congrFun h.1 7
  ext i
  fin_cases i <;> simp [h0,h2,h3,h4,h6]

theorem annihilator_basis_seven (x : Carrier F)
    (h : mul (basisVector 7) x = 0 ∧ mul x (basisVector 7) = 0) :
    x = ![0,0,0,0,0,x 5,x 6,x 7] := by
  have h0 : x 0 = 0 := by simpa [mul,basisVector] using congrFun h.1 4
  have h1 : x 1 = 0 := by simpa [mul,basisVector] using congrFun h.1 5
  have h2 : x 2 = 0 := by simpa [mul,basisVector] using congrFun h.1 6
  have h3 : x 3 = 0 := by simpa [mul,basisVector] using congrFun h.1 7
  have h4 : x 4 = 0 := by simpa [mul,basisVector] using congrFun h.2 7
  ext i
  fin_cases i <;> simp [h0,h1,h2,h3,h4]

/-- Eliminate the third point after the first two are the lines of vectors 0 and 1. -/
def thirdReducer (x : Carrier F) : Model F :=
  rootC (x 1 / x 5) * rootB (x 0 / x 5)

theorem thirdReducer_fixes (x : Carrier F) :
    (thirdReducer x).val (basisVector 0) = basisVector 0 ∧
    (thirdReducer x).val (basisVector 1) = basisVector 1 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [thirdReducer,rootB,rootC,rootBEquiv,rootCEquiv,
      rootBLinear,rootCLinear,rootBApply,rootCApply,basisVector]

theorem thirdReducer_apply (x : Carrier F)
    (hx : x = ![x 0,x 1,0,0,0,x 5,0,0]) (h5 : x 5 ≠ 0) :
    (thirdReducer x).val x = x 5 • basisVector 5 := by
  have h2 : x 2 = 0 := congrFun hx 2
  have h3 : x 3 = 0 := congrFun hx 3
  have h4 : x 4 = 0 := congrFun hx 4
  have h6 : x 6 = 0 := congrFun hx 6
  have h7 : x 7 = 0 := congrFun hx 7
  ext i
  fin_cases i <;>
    simp [thirdReducer,rootB,rootC,rootBEquiv,rootCEquiv,
      rootBLinear,rootCLinear,rootBApply,rootCApply,basisVector,h2,h3,h4,h6,h7,h5]

/-- Eliminate the fourth point while fixing the first three coordinate vectors. -/
def fourthReducer (x : Carrier F) : Model F :=
  rootA (-x 1 / x 7) * rootD (-x 5 / x 7)

theorem fourthReducer_fixes (x : Carrier F) :
    (fourthReducer x).val (basisVector 0) = basisVector 0 ∧
    (fourthReducer x).val (basisVector 1) = basisVector 1 ∧
    (fourthReducer x).val (basisVector 5) = basisVector 5 := by
  repeat' constructor
  all_goals ext i; fin_cases i <;>
    simp [fourthReducer,rootA,rootD,rootAEquiv,rootDEquiv,
      rootALinear,rootDLinear,rootAApply,rootDApply,basisVector]

theorem fourthReducer_apply (x : Carrier F)
    (hx : x = ![0,x 1,0,0,0,x 5,0,x 7]) (h7 : x 7 ≠ 0) :
    (fourthReducer x).val x = x 7 • basisVector 7 := by
  have h0 : x 0 = 0 := congrFun hx 0
  have h2 : x 2 = 0 := congrFun hx 2
  have h3 : x 3 = 0 := congrFun hx 3
  have h4 : x 4 = 0 := congrFun hx 4
  have h6 : x 6 = 0 := congrFun hx 6
  ext i
  fin_cases i <;>
    simp [fourthReducer,rootA,rootD,rootAEquiv,rootDEquiv,
      rootALinear,rootDLinear,rootAApply,rootDApply,basisVector,h0,h2,h3,h4,h6,h7]

theorem rootE_fixes_prefix (a : F) :
    (rootE a).val (basisVector 0) = basisVector 0 ∧
    (rootE a).val (basisVector 1) = basisVector 1 ∧
    (rootE a).val (basisVector 5) = basisVector 5 ∧
    (rootE a).val (basisVector 7) = basisVector 7 := by
  repeat' constructor
  all_goals ext i; fin_cases i <;>
    simp [rootE,rootEEquiv,rootELinear,rootEApply,basisVector]

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
