/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianDeterminantRows.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGlue

/-!
# IcosianDeterminantRows

A nonzero two-entry row determines a determinant functional with fibers
parametrized by the field. Solving for one coordinate gives the fiber
equivalence and its cardinality.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianDeterminantRows.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas.Codes
open scoped Matrix
attribute [local instance] Classical.propDecidable

abbrev IcosianRow (F : Type*) := Fin 2 → F

def icosianRowDet {F : Type*} [CommRing F] (x y : IcosianRow F) : F :=
  x 0*y 1-x 1*y 0

def IcosianDetRow {F : Type*} [Field F] (y : IcosianRow F) (d : F) :=
  {x : IcosianRow F // icosianRowDet x y=d}

noncomputable def icosianDetRowParameter {F : Type*} [Field F]
    (y : IcosianRow F) (d t : F) : IcosianRow F :=
  if y 1=0 then ![t,-d/y 0] else ![(d+t*y 0)/y 1,t]

theorem icosianRow_zero_first {F : Type*} [Field F] (y : IcosianRow F)
    (hy : y≠0) (h1 : y 1=0) : y 0≠0 := by
  intro h0
  apply hy
  funext i
  fin_cases i <;> assumption

theorem icosianDetRowParameter_det {F : Type*} [Field F]
    (y : IcosianRow F) (hy : y≠0) (d t : F) :
    icosianRowDet (icosianDetRowParameter y d t) y=d := by
  classical
  by_cases h1 : y 1=0
  · have h0 := icosianRow_zero_first y hy h1
    simp [icosianDetRowParameter,h1,icosianRowDet,h0]
  · simp [icosianDetRowParameter,h1,icosianRowDet]

noncomputable def icosianDetRowEquiv {F : Type*} [Field F]
    (y : IcosianRow F) (hy : y≠0) (d : F) : F ≃ IcosianDetRow y d where
  toFun t := ⟨icosianDetRowParameter y d t,icosianDetRowParameter_det y hy d t⟩
  invFun x := if y 1=0 then x.val 0 else x.val 1
  left_inv t := by
    classical
    by_cases h : y 1=0 <;> simp [icosianDetRowParameter,h]
  right_inv x := by
    classical
    apply Subtype.ext
    have hx := x.property
    unfold icosianRowDet at hx
    funext i
    fin_cases i
    · by_cases h1 : y 1=0
      · simp [icosianDetRowParameter,h1]
      · simp [icosianDetRowParameter,h1]
        apply (div_eq_iff h1).mpr
        linear_combination -hx
    · by_cases h1 : y 1=0
      · have h0 := icosianRow_zero_first y hy h1
        simp [icosianDetRowParameter,h1]
        apply (div_eq_iff h0).mpr
        simp only [h1,mul_zero,zero_sub] at hx
        linear_combination hx
      · simp [icosianDetRowParameter,h1]

theorem icosianDetRow_card {F : Type*} [Field F] [Finite F]
    (y : IcosianRow F) (hy : y≠0) (d : F) :
    Nat.card (IcosianDetRow y d)=Nat.card F :=
  (Nat.card_congr (icosianDetRowEquiv y hy d)).symm

end Atlas.Codes
