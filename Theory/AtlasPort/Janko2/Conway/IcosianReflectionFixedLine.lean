/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionFixedLine.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel

/-!
# IcosianReflectionFixedLine

A root reflection negates its root and therefore fixes its projective line.
Coordinate evaluation shows axis reflections are not central signs.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionFixedLine.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianReflection_self (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) : icosianReflection r r= -r := by
  funext i
  simp [icosianReflection,hr,icosianRightMul,mul_two]

theorem icosianLineReflection_fixes (p : IcosianRootPoint) :
    icosianLineReflection p • p=p := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [icosianLineReflection_root]
  apply Subtype.ext
  change icosianRootReflectionOf r • icosianRootPoint r=icosianRootPoint r
  rw [icosianRootPoint,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (-1 : IcosianQuaternion),?_⟩
  change MulOpposite.op (-1 : IcosianQuaternion) • icosianCoordinateEmbedding r.val=
    (icosianRootReflectionOf r).val (icosianCoordinateEmbedding r.val)
  rw [icosianRootReflectionOf_apply,icosianReflection_self _ r.property.2]
  funext i
  simp

theorem icosianAxisReflection_not_sign (i : Fin 3) :
    icosianAxisReflection i∉icosianCentralSigns := by
  intro h
  rcases h with h|h
  · have he := congrArg
      (fun g : icosianHermitianGroup => g.val (Pi.single i 1 : IcosianRationalCoordinates) i) h
    rw [icosianAxisReflection_apply] at he
    have hh : -(1 : GoldenRational)=1 := by
      simpa using congrArg QuaternionAlgebra.re he
    exact one_ne_zero (CharZero.neg_eq_self_iff.mp hh)
  · obtain ⟨j,hji⟩ := exists_ne i
    have he := congrArg
      (fun g : icosianHermitianGroup => g.val (Pi.single j 1 : IcosianRationalCoordinates) j) h
    rw [icosianAxisReflection_apply,icosianCentralSign_apply] at he
    have hh : (1 : GoldenRational)= -1 := by
      simpa [hji] using congrArg QuaternionAlgebra.re he
    exact one_ne_zero (CharZero.eq_neg_self_iff.mp hh)

end Atlas.Conway
