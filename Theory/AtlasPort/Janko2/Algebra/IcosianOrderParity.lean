/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianOrderParity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianOrderBasis
public import Theory.AtlasPort.Janko2.Algebra.IcosianCoordinateNorm
public import Mathlib.Algebra.CharP.Two

/-!
# IcosianOrderParity

Twice the rational coordinates of an integral icosian belong to the
binary parity code. Explicit basis synthesis gives the integer coordinates
and their parity-code parameters.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianOrderParity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open Atlas.Codes
open scoped Quaternion QuadraticAlgebra BigOperators

/-- Twice the eight rational coordinates of an integral icosian. -/
def icosianIntegralDouble (a : Fin 4 → GoldenInteger) : IcosianIntegerCoordinates :=
  ![2*(a 0).re+(a 2).re-(a 3).re+(a 3).im,
    2*(a 0).im+(a 2).im+(a 3).re,
    2*(a 1).re+(a 2).re-(a 2).im+(a 3).re,
    2*(a 1).im-(a 2).re+(a 3).im,
    -(a 3).im,-(a 3).re-(a 3).im,(a 2).im,(a 2).re+(a 2).im]

theorem icosianIntegralDouble_synthesis (a : Fin 4 → GoldenInteger) :
    icosianCoordinatesQuaternion (icosianIntegralDouble a)=
      icosianBasisSynthesis (fun i => goldenIntegerToRational (a i)) := by
  ext <;> simp [icosianCoordinatesQuaternion,icosianIntegralDouble,
    icosianBasisSynthesis,goldenIntegerToRational,icosianGenerator,icosianI] <;> ring

theorem icosianIntegralDouble_parity (a : Fin 4 → GoldenInteger) :
    (fun i => (icosianIntegralDouble a i : Bit)) ∈ icosianParity := by
  refine ⟨![(a 2).re,(a 2).im,(a 3).re,(a 3).im],?_⟩
  funext j
  fin_cases j <;> simp [icosianParityEncoder,icosianParityRows,
    icosianIntegralDouble,Fin.sum_univ_succ,CharTwo.sub_eq_add,CharTwo.neg_eq] <;> ring

theorem isIcosian_has_parity_coordinates {x : IcosianQuaternion} (hx : IsIcosian x) :
    ∃ v : IcosianIntegerCoordinates,
      (fun i => (v i : Bit)) ∈ icosianParity ∧ icosianCoordinatesQuaternion v=x := by
  obtain ⟨a,rfl⟩ := (isIcosian_iff_synthesis x).mp hx
  exact ⟨icosianIntegralDouble a,icosianIntegralDouble_parity a,
    icosianIntegralDouble_synthesis a⟩

end Atlas.Algebra
