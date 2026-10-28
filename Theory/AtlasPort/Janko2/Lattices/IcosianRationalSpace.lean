/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRationalSpace.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianQuaternion
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechForm

/-!
# Icosian Rational Space

Three quaternions over the golden rational field form the rational
ambient space. Expanding their eight rational coordinates identifies
the weighted Hermitian trace pairing with the ordinary 24-coordinate dot product.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRationalSpace.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion QuadraticAlgebra Matrix

abbrev IcosianRationalCoordinates := Fin 3 → IcosianQuaternion
abbrev IcosianRealIndex := Fin 3 × (Fin 4 × Fin 2)

def icosianHermitian (x y : IcosianRationalCoordinates) : IcosianQuaternion :=
  (1/2 : ℚ) • ∑ i, star (x i) * y i

def icosianBilinear (x y : IcosianRationalCoordinates) : ℚ :=
  2 * icosianFunctional (icosianHermitian x y)

def icosianQuaternionCoordinate (x : IcosianQuaternion) (i : Fin 4) : GoldenRational :=
  ![x.re,x.imI,x.imJ,x.imK] i

def icosianRealCoordinates :
    IcosianRationalCoordinates ≃ₗ[ℚ] (IcosianRealIndex → ℚ) where
  toFun z p := if p.2.2=0 then (icosianQuaternionCoordinate (z p.1) p.2.1).re
    else (icosianQuaternionCoordinate (z p.1) p.2.1).im
  invFun x i := ⟨⟨x (i,0,0),x (i,0,1)⟩,⟨x (i,1,0),x (i,1,1)⟩,
    ⟨x (i,2,0),x (i,2,1)⟩,⟨x (i,3,0),x (i,3,1)⟩⟩
  left_inv z := by funext i; ext <;> simp [icosianQuaternionCoordinate]
  right_inv x := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]
  map_add' z w := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]
  map_smul' r z := by
    funext ⟨i,j,k⟩
    fin_cases j <;> fin_cases k <;> simp [icosianQuaternionCoordinate]

theorem icosianBilinear_eq_dot (z w : IcosianRationalCoordinates) :
    icosianBilinear z w = dotProduct (icosianRealCoordinates z) (icosianRealCoordinates w) := by
  simp [icosianBilinear,icosianHermitian,icosianFunctional,goldenFunctional,
    Quaternion.re_mul,icosianRealCoordinates,icosianQuaternionCoordinate,dotProduct,
    Fintype.sum_prod_type,Fin.sum_univ_succ,Finset.sum_add_distrib]
  ring

end Atlas.Lattices
