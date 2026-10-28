/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionIsometries.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianCentralizerFinite
public import Theory.AtlasPort.Janko2.Lattices.IcosianHermitianIntegral

/-!
# IcosianReflectionIsometries

A norm-two lattice root defines an involutory rational-linear Hermitian isometry. The
reflection formula proves linearity, isometry, and lattice preservation.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionIsometries.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- The norm-two quaternionic reflection as a rational linear equivalence. -/
def icosianReflectionEquiv (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) :
    IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates where
  toFun := icosianReflection r
  invFun := icosianReflection r
  left_inv := icosianReflection_involutive r hr
  right_inv := icosianReflection_involutive r hr
  map_add' x y := by
    funext i
    simp [icosianReflection,icosianHermitian_add_right,icosianRightMul,mul_add]
    abel
  map_smul' a x := by
    funext i
    simp [icosianReflection,icosianHermitian_smul_right,icosianRightMul,
      smul_sub,Algebra.mul_smul_comm (R := ℚ) (A := IcosianQuaternion)]

theorem icosianReflectionEquiv_mem (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) (hL : r ∈ rationalIcosianLattice) :
    icosianReflectionEquiv r hr ∈ icosianHermitianGroup := by
  refine ⟨?_,fun x y => icosianReflection_hermitian r x y hr,?_⟩
  · intro a x
    funext i
    simp [icosianReflectionEquiv,icosianReflection,icosianHermitian_rightMul_right,
      icosianRightMul,sub_mul,mul_assoc]
  · intro x
    constructor
    · exact fun hx => icosianReflection_lattice hL hx
    · intro hx
      have h := icosianReflection_lattice hL hx
      change icosianReflection r (icosianReflection r x) ∈ rationalIcosianLattice at h
      rwa [icosianReflection_involutive r hr x] at h

/-- An actual reflection in the full Hermitian lattice stabilizer. -/
def icosianRootReflection (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) (hL : r ∈ rationalIcosianLattice) :
    icosianHermitianGroup := ⟨icosianReflectionEquiv r hr,icosianReflectionEquiv_mem r hr hL⟩

theorem icosianRootReflection_square (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) (hL : r ∈ rationalIcosianLattice) :
    icosianRootReflection r hr hL*icosianRootReflection r hr hL=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact icosianReflection_involutive r hr x

end Atlas.Conway
