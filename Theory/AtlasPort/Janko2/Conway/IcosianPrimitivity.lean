/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianPrimitivity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianSixSuborbits
public import Theory.AtlasPort.Janko2.Conway.IcosianIwasawa
public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveGeometryTransport
public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-!
# IcosianPrimitivity

The six subdegrees are 1, 10, 160, 80, 32, and 32. Their possible block sums and
divisibility by 315 force primitivity, which descends to the sign quotient.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianPrimitivity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators

def icosianRootSuborbitLabel (p : IcosianRootPoint) : Fin 6 :=
  (icosianRootPointNormLevel_exhaustive p 0).choose

theorem icosianRootSuborbitLabel_spec (p : IcosianRootPoint) :
    icosianRootPointNormWord p 0=icosianRootCoordinateLevels (icosianRootSuborbitLabel p) :=
  (icosianRootPointNormLevel_exhaustive p 0).choose_spec

theorem icosianRootSuborbitLabel_eq_iff (p : IcosianRootPoint) (i : Fin 6) :
    icosianRootSuborbitLabel p=i ↔ icosianRootPointNormWord p 0=icosianRootCoordinateLevels i := by
  constructor
  · rintro rfl
    exact icosianRootSuborbitLabel_spec p
  · intro h
    exact icosianRootCoordinateLevels_injective ((icosianRootSuborbitLabel_spec p).symm.trans h)

def icosianRootSubdegree : Fin 6 → ℕ := ![1,10,160,80,32,32]

theorem icosianRootSuborbitLabel_fiber_card (i : Fin 6) :
    Nat.card {p : IcosianRootPoint // icosianRootSuborbitLabel p=i}=icosianRootSubdegree i := by
  have he : {p : IcosianRootPoint | icosianRootSuborbitLabel p=i}=
      {p : IcosianRootPoint | icosianRootPointNormWord p 0=icosianRootCoordinateLevels i} :=
    Set.ext (fun p => icosianRootSuborbitLabel_eq_iff p i)
  change Nat.card ({p : IcosianRootPoint | icosianRootSuborbitLabel p=i} : Set IcosianRootPoint)=_
  rw [Nat.card_congr (Equiv.setCongr he)]
  exact icosianRootPointNormLevel_six_card i

theorem icosianRootSuborbitLabel_axis : icosianRootSuborbitLabel (icosianRootAxisPoint 0)=0 := by
  apply (icosianRootSuborbitLabel_eq_iff _ _).mpr
  change icosianRootPointNormWord (icosianRootToPoint (icosianAxisRoot (0,1))) 0=4
  rw [icosianRootPointNormWord_toPoint]
  apply icosianRootNormWord_of_norm
  simpa only [map_ofNat] using
    icosianRoot_single_norm (icosianAxisRoot (0,1)) 0
      (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])

/-- Exactly32 labelled unions contain the singleton base orbit. -/
theorem icosian_six_suborbit_block_arithmetic : ∀ T : Finset (Fin 6),
    0∈T → (∑ i∈T,icosianRootSubdegree i)∣315 →
      (∑ i∈T,icosianRootSubdegree i)=1 ∨ (∑ i∈T,icosianRootSubdegree i)=315 := by
  decide +kernel

theorem icosianHermitian_rootPoint_primitive :
    MulAction.IsPreprimitive icosianHermitianGroup IcosianRootPoint := by
  refine Atlas.GroupTheory.primitive_of_suborbit_sums (icosianRootAxisPoint 0)
    icosianRootSuborbitLabel ?_ icosianRootSubdegree icosianRootSuborbitLabel_fiber_card ?_
  · intro p q hpq
    change q∈MulAction.orbit icosianFullAxisStabilizer p
    rw [icosianFullAxisStabilizer_orbit]
    exact (icosianRootSuborbitLabel_spec q).trans
      ((congrArg icosianRootCoordinateLevels hpq.symm).trans (icosianRootSuborbitLabel_spec p).symm)
  · intro T hT hd
    rw [icosianRootSuborbitLabel_axis] at hT
    rw [icosianRootPoint_card] at hd ⊢
    exact icosian_six_suborbit_block_arithmetic T hT hd

theorem icosianProjective_rootPoint_primitive :
    MulAction.IsPreprimitive IcosianProjectiveModel IcosianRootPoint := by
  let := icosianHermitian_rootPoint_primitive
  exact icosianProjective_primitive_of_linear

end Atlas.Conway
