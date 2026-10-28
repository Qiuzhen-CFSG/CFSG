/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianScalarIsometries.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianIntegralComparison
public import Theory.AtlasPort.Janko2.Lattices.IcosianScalarCommutation
public import Theory.AtlasPort.Janko2.LinearAlgebra.AutomorphismCongr

/-!
# IcosianScalarIsometries

The icosian-to-Leech comparison transports right-unit scalar isometries into the
Leech isometry group. Their centralizer is the concrete subgroup used for the
Hermitian model.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianScalarIsometries.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.LinearAlgebra

def icosianAutomorphismComparison := linearAutomorphismCongr icosianComparison

def icosianRationalScalar (u : icosianNormOneGroup) :=
  icosianAutomorphismComparison (icosianScalarRepresentation u)

theorem icosianRationalScalar_mem (u : icosianNormOneGroup) :
    icosianRationalScalar u ∈ rationalLatticeIsometries := by
  constructor
  · intro x y
    change rationalForm (icosianComparison (icosianScalarRepresentation u (icosianComparison.symm x)))
      (icosianComparison (icosianScalarRepresentation u (icosianComparison.symm y))) = _
    rw [icosianComparison_isometry,icosianScalarRepresentation_bilinear]
    have h := icosianComparison_isometry (icosianComparison.symm x) (icosianComparison.symm y)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  · intro x
    have h := (icosianComparison_lattice_iff (icosianComparison.symm x)).symm.trans
      ((icosianScalarRepresentation_lattice_iff u (icosianComparison.symm x)).trans
        (icosianComparison_lattice_iff (icosianScalarRepresentation u (icosianComparison.symm x))))
    change x ∈ rationalLeech ↔
      icosianComparison (icosianScalarRepresentation u (icosianComparison.symm x)) ∈ rationalLeech
    simpa only [LinearEquiv.apply_symm_apply] using h

def icosianScalarsToRational : icosianNormOneGroup →* rationalLatticeIsometries where
  toFun u := ⟨icosianRationalScalar u,icosianRationalScalar_mem u⟩
  map_one' := by apply Subtype.ext; simp [icosianRationalScalar]
  map_mul' u v := by apply Subtype.ext; simp [icosianRationalScalar]

/-- The actual right icosian norm-one scalars embedded in the retained Co0 model. -/
def icosianScalarsToCo0 : icosianNormOneGroup →* LeechIsometryGroup :=
  fullIsometryEquiv.symm.toMonoidHom.comp icosianScalarsToRational

theorem icosianScalarsToCo0_extension (u : icosianNormOneGroup) :
    fullIsometryEquiv (icosianScalarsToCo0 u)=icosianScalarsToRational u :=
  fullIsometryEquiv.apply_symm_apply _

/-- The full centralizer of the actual right norm-one scalar group. -/
def icosianCentralizer : Subgroup LeechIsometryGroup :=
  Subgroup.centralizer (Set.range icosianScalarsToCo0)

theorem icosianCentralizer_mem (g : LeechIsometryGroup) :
    g ∈ icosianCentralizer ↔ ∀ u,g*icosianScalarsToCo0 u=icosianScalarsToCo0 u*g := by
  simp only [icosianCentralizer,Subgroup.mem_centralizer_iff,Set.forall_mem_range]
  exact forall_congr' (fun u => eq_comm)

end Atlas.Conway
