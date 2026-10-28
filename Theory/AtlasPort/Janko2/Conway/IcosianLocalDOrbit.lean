/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalDOrbit.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalDStabilizerBound
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCOrbit
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# IcosianLocalDOrbit

The shape-D root points form one full frame-stabilizer orbit. A stabilizer bound and
the known shape count force orbit exhaustion and exact orders.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalDOrbit.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

attribute [local instance] icosianLiftedRootPointAction

def icosianLocalDOrbitToShape
    (p : MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot)) :
    IcosianRootPointShape 3 := by
  refine ⟨p.val,?_⟩
  obtain ⟨g,hg⟩ := p.property
  refine ⟨icosianMonomialToHermitian g • icosianLocalDRoot,?_,
    (icosianMonomialRoot_shape g icosianLocalDRoot 3).mpr icosianLocalDRoot_shape⟩
  have h := congrArg Subtype.val hg
  exact (icosianRootPoint_smul _ _).trans h

theorem icosianLocalDOrbitToShape_injective : Function.Injective icosianLocalDOrbitToShape := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : IcosianRootPointShape 3 => z.val) h

def icosianLocalDStabilizerEquiv :
    MulAction.stabilizer icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot) ≃
      icosianLocalDStabilizer :=
  Equiv.subtypeEquivRight (fun g => by
    change (icosianMonomialToHermitian g • icosianRootToPoint icosianLocalDRoot=
      icosianRootToPoint icosianLocalDRoot) ↔
      icosianMonomialToHermitian g • icosianRootPoint icosianLocalDRoot=
        icosianRootPoint icosianLocalDRoot
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩)

theorem icosianLocalDOrbit_card :
    Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot))=96 := by
  have hl := Nat.card_le_card_of_injective icosianLocalDOrbitToShape
    icosianLocalDOrbitToShape_injective
  rw [icosianRootPointShape_card] at hl
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalDStabilizerEquiv,icosianLiftedMonomial_card] at he
  have hb := icosianLocalDStabilizer_card_le
  change Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot))≤96 at hl
  nlinarith

theorem icosianLocalDStabilizer_card : Nat.card icosianLocalDStabilizer=24 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalDRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalDStabilizerEquiv,
    icosianLiftedMonomial_card,icosianLocalDOrbit_card] at he
  omega

/-- The full actual monomial group is transitive on the96 D-type root lines.
This follows from the scalar stabilizer bound and the independently counted family. -/
theorem icosianLocalDOrbit_exhaustive (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 3 ↔
      ∃ g : icosianLiftedMonomial,icosianMonomialToHermitian g •
        icosianRootToPoint icosianLocalDRoot=p := by
  have hs : Function.Surjective icosianLocalDOrbitToShape :=
    ((Nat.bijective_iff_injective_and_card icosianLocalDOrbitToShape).mpr
      ⟨icosianLocalDOrbitToShape_injective,by
        rw [icosianLocalDOrbit_card,icosianRootPointShape_card]; rfl⟩).2
  constructor
  · intro hp
    obtain ⟨q,hq⟩ := hs ⟨p,hp⟩
    have he : q.val=p := congrArg Subtype.val hq
    obtain ⟨g,hg⟩ := q.property
    exact ⟨g,hg.trans he⟩
  · rintro ⟨g,rfl⟩
    exact (icosianLocalDOrbitToShape ⟨_,⟨g,rfl⟩⟩).property

theorem icosianLocalD_full_frame_orbit (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 3 ↔
      ∃ g : icosianCoordinateFrameStabilizer,g.val • icosianRootToPoint icosianLocalDRoot=p := by
  constructor
  · intro hp
    obtain ⟨g,hg⟩ := (icosianLocalDOrbit_exhaustive p).mp hp
    exact ⟨⟨icosianMonomialToHermitian g,icosianMonomial_mem_frameStabilizer g⟩,hg⟩
  · rintro ⟨g,rfl⟩
    exact (icosianCoordinateFrame_rootPoint_shape g (icosianRootToPoint icosianLocalDRoot) 3).mpr
      ⟨icosianLocalDRoot,rfl,icosianLocalDRoot_shape⟩

theorem icosianLocalD_full_frame_stabilizer_card :
    Nat.card (MulAction.stabilizer icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalDRoot))=24 := by
  have heq : MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalDRoot)={p : IcosianRootPoint | HasIcosianRootPointShape p 3} := by
    ext p
    exact (icosianLocalD_full_frame_orbit p).symm
  have ho : Nat.card (MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalDRoot))=96 := by
    rw [Nat.card_congr (Equiv.setCongr heq)]
    exact icosianRootPointShape_card 3
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianCoordinateFrameStabilizer (icosianRootToPoint icosianLocalDRoot))
  rw [Nat.card_prod,ho,icosianCoordinateFrameStabilizer_card] at h
  omega

end Atlas.Conway
