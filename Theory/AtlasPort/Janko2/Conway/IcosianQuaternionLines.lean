/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianQuaternionLines.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianCentralizer
public import Theory.AtlasPort.Janko2.Algebra.IcosianDivision
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# IcosianQuaternionLines

Right quaternionic projective lines use the opposite division ring. The Hermitian
action commutes with right scalars and acts on the three coordinate axes.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianQuaternionLines.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Pointwise

/-- Right quaternionic lines, using mathlib projectivization over the opposite division ring. -/
abbrev IcosianQuaternionPoint := Projectivization IcosianQuaternionᵐᵒᵖ IcosianRationalCoordinates

instance icosianHermitian_comm_right_scalars :
    SMulCommClass icosianHermitianGroup IcosianQuaternionᵐᵒᵖ IcosianRationalCoordinates where
  smul_comm g a x := g.property.1 (MulOpposite.unop a) x

/-- The coordinate quaternionic line, not a chosen root representative. -/
def icosianAxisPoint (i : Fin 3) : IcosianQuaternionPoint :=
  Projectivization.mk _ (Pi.single i (1 : IcosianQuaternion)) (by
    intro h
    have hi := congrFun h i
    simp at hi)

theorem icosianAxisPoint_injective : Function.Injective icosianAxisPoint := by
  intro i j h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h
  by_contra hij
  have hi := congrFun ha i
  simp [hij] at hi

def icosianCoordinateFrame : Set IcosianQuaternionPoint := Set.range icosianAxisPoint

def icosianCoordinateFrameStabilizer : Subgroup icosianHermitianGroup :=
  MulAction.stabilizer icosianHermitianGroup icosianCoordinateFrame

end Atlas.Conway
