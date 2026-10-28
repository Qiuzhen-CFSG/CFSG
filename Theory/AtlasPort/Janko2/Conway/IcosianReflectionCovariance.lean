/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionCovariance.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionIsometries
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneGroup

/-!
# IcosianReflectionCovariance

Unit multiples define the same root reflection, and Hermitian maps conjugate
reflections equivariantly. Pointwise quaternionic formulas prove both identities.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionCovariance.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianReflection_unit_multiple (r v : IcosianRationalCoordinates)
    (u : icosianNormOneGroup) :
    icosianReflection (icosianRightMul r u.val.val) v=icosianReflection r v := by
  simp only [icosianReflection,icosianHermitian_rightMul_left]
  congr 1
  funext i
  change (r i*u.val.val)*(star u.val.val*icosianHermitian r v)=_
  have hu : u.val.val*star u.val.val=1 := Unitary.coe_mul_star_self u.val
  calc
    _=r i*(u.val.val*star u.val.val)*icosianHermitian r v := by simp only [mul_assoc]
    _=r i*icosianHermitian r v := by rw [hu,mul_one]

theorem icosianReflection_covariance (f : icosianHermitianGroup)
    (r v : IcosianRationalCoordinates) :
    f.val (icosianReflection r v)=icosianReflection (f.val r) (f.val v) := by
  simp only [icosianReflection,map_sub,f.property.1,f.property.2.1]

theorem icosianRootReflection_apply (r v : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) (hL : r∈rationalIcosianLattice) :
    (icosianRootReflection r hr hL).val v=icosianReflection r v := rfl

theorem icosianRootReflection_conjugate (f : icosianHermitianGroup)
    (r : IcosianRationalCoordinates) (hr : icosianHermitian r r=2)
    (hL : r∈rationalIcosianLattice) :
    f*icosianRootReflection r hr hL*f⁻¹=
      icosianRootReflection (f.val r) (by rw [f.property.2.1,hr])
        ((f.property.2.2 r).mp hL) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change f.val (icosianReflection r (f.val.symm x))=icosianReflection (f.val r) x
  rw [icosianReflection_covariance,f.val.apply_symm_apply]

end Atlas.Conway
