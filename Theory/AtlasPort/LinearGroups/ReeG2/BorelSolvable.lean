module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/BorelSolvable.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Borel
public import Theory.AtlasPort.LinearGroups.ReeG2.RootSolvable
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
variable (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
set_option maxHeartbeats 2000000

theorem borelParam_col_zero (p : (F × F × F) × Fˣ) (i : Fin 7) :
    (borelParam m p).val i 0 = if i = 0 then theta F m (p.2 : F) else 0 := by
  change (rootMatrix m p.1.1 p.1.2.1 p.1.2.2 *
    Matrix.diagonal (fun i => (torusDiagonal m p.2 i : F))) i 0 = _
  rw [Matrix.mul_diagonal]
  fin_cases i <;> simp [rootMatrix_expanded, rootExpanded, torusDiagonal]

theorem borel_mul_zero_zero (g h : borel m hcard) :
    (g*h).val.val 0 0 = g.val.val 0 0 * h.val.val 0 0 := by
  obtain ⟨p,rfl⟩ := (borelEquiv m hcard).surjective g
  obtain ⟨q,rfl⟩ := (borelEquiv m hcard).surjective h
  change ((borelParam m p).val * (borelParam m q).val) 0 0 =
    (borelParam m p).val 0 0 * (borelParam m q).val 0 0
  rw [Matrix.mul_apply]
  simp [borelParam_col_zero, Fin.sum_univ_succ, borelParam_00]

def borelTorusParameter (g : borel m hcard) : Fˣ := ((borelEquiv m hcard).symm g).2

theorem borelTorusParameter_zero_zero (g : borel m hcard) :
    theta F m (borelTorusParameter m hcard g : F) = g.val.val 0 0 := by
  have h := borelParam_00 m ((borelEquiv m hcard).symm g)
  change ((borelEquiv m hcard ((borelEquiv m hcard).symm g)).val).val 0 0 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

def borelTorusProjection : borel m hcard →* Fˣ where
  toFun := borelTorusParameter m hcard
  map_one' := by
    apply Units.ext
    apply (theta F m).injective
    rw [borelTorusParameter_zero_zero]
    simp
  map_mul' := by
    intro g h
    apply Units.ext
    apply (theta F m).injective
    change theta F m (borelTorusParameter m hcard (g*h) : F) =
      theta F m ((borelTorusParameter m hcard g : F) * (borelTorusParameter m hcard h : F))
    rw [map_mul, borelTorusParameter_zero_zero, borelTorusParameter_zero_zero,
      borelTorusParameter_zero_zero, borel_mul_zero_zero]

def rootToBorel : rootSubgroup m hcard →* borel m hcard :=
  Subgroup.inclusion le_sup_left

theorem borelTorusProjection_ker_le_range :
    (borelTorusProjection m hcard).ker ≤ (rootToBorel m hcard).range := by
  intro g hg
  obtain ⟨⟨p,l⟩,rfl⟩ := (borelEquiv m hcard).surjective g
  change ((borelEquiv m hcard).symm (borelEquiv m hcard (p,l))).2 = 1 at hg
  rw [Equiv.symm_apply_apply] at hg
  change l = 1 at hg
  subst l
  refine ⟨⟨rootElement m p.1 p.2.1 p.2.2,⟨p,rfl⟩⟩,?_⟩
  apply Subtype.ext
  change rootElement m p.1 p.2.1 p.2.2 = rootElement m p.1 p.2.1 p.2.2 * torus m 1
  have ht : torus (F := F) m 1 = 1 := (torusHom m).map_one
  rw [ht, mul_one]

theorem borel_solvable : Group.IsSolvable (borel m hcard) := by
  letI := rootSubgroup_solvable m hcard
  exact Group.isSolvable_of_ker_le_range (rootToBorel m hcard)
    (borelTorusProjection m hcard) (borelTorusProjection_ker_le_range m hcard)
end Atlas.ReeG2
