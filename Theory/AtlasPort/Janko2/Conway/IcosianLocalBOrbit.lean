/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalBOrbit.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalBStabilizerBound
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCOrbit
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# IcosianLocalBOrbit

The shape-B root points form one full frame-stabilizer orbit. A stabilizer bound and
the known shape count force orbit exhaustion and exact orders.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalBOrbit.lean`, revision
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

def icosianLocalBOrbitToShape
    (p : MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot)) :
    IcosianRootPointShape 1 := by
  refine ⟨p.val,?_⟩
  obtain ⟨g,hg⟩ := p.property
  refine ⟨icosianMonomialToHermitian g • icosianLocalBRoot,?_,
    (icosianMonomialRoot_shape g icosianLocalBRoot 1).mpr icosianLocalBRoot_shape⟩
  have h := congrArg Subtype.val hg
  exact (icosianRootPoint_smul _ _).trans h

theorem icosianLocalBOrbitToShape_injective : Function.Injective icosianLocalBOrbitToShape := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : IcosianRootPointShape 1 => z.val) h

def icosianLocalBStabilizerEquiv :
    MulAction.stabilizer icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot) ≃
      icosianLocalBStabilizer :=
  Equiv.subtypeEquivRight (fun g => by
    change (icosianMonomialToHermitian g • icosianRootToPoint icosianLocalBRoot=
      icosianRootToPoint icosianLocalBRoot) ↔
      icosianMonomialToHermitian g • icosianRootPoint icosianLocalBRoot=
        icosianRootPoint icosianLocalBRoot
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩)

theorem icosianLocalBOrbit_card :
    Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot))=24 := by
  have hl := Nat.card_le_card_of_injective icosianLocalBOrbitToShape
    icosianLocalBOrbitToShape_injective
  rw [icosianRootPointShape_card] at hl
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalBStabilizerEquiv,icosianLiftedMonomial_card] at he
  have hb := icosianLocalBStabilizer_card_le
  change Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot))≤24 at hl
  nlinarith

theorem icosianLocalBStabilizer_card : Nat.card icosianLocalBStabilizer=96 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalBRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalBStabilizerEquiv,
    icosianLiftedMonomial_card,icosianLocalBOrbit_card] at he
  omega

/-- The full actual monomial group is transitive on the24 B-type root lines.
This follows from the scalar stabilizer bound and the independently counted family. -/
theorem icosianLocalBOrbit_exhaustive (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 1 ↔
      ∃ g : icosianLiftedMonomial,icosianMonomialToHermitian g •
        icosianRootToPoint icosianLocalBRoot=p := by
  have hs : Function.Surjective icosianLocalBOrbitToShape :=
    ((Nat.bijective_iff_injective_and_card icosianLocalBOrbitToShape).mpr
      ⟨icosianLocalBOrbitToShape_injective,by
        rw [icosianLocalBOrbit_card,icosianRootPointShape_card]; rfl⟩).2
  constructor
  · intro hp
    obtain ⟨q,hq⟩ := hs ⟨p,hp⟩
    have he : q.val=p := congrArg Subtype.val hq
    obtain ⟨g,hg⟩ := q.property
    exact ⟨g,hg.trans he⟩
  · rintro ⟨g,rfl⟩
    exact (icosianLocalBOrbitToShape ⟨_,⟨g,rfl⟩⟩).property

theorem icosianLocalB_full_frame_orbit (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 1 ↔
      ∃ g : icosianCoordinateFrameStabilizer,g.val • icosianRootToPoint icosianLocalBRoot=p := by
  constructor
  · intro hp
    obtain ⟨g,hg⟩ := (icosianLocalBOrbit_exhaustive p).mp hp
    exact ⟨⟨icosianMonomialToHermitian g,icosianMonomial_mem_frameStabilizer g⟩,hg⟩
  · rintro ⟨g,rfl⟩
    exact (icosianCoordinateFrame_rootPoint_shape g (icosianRootToPoint icosianLocalBRoot) 1).mpr
      ⟨icosianLocalBRoot,rfl,icosianLocalBRoot_shape⟩

theorem icosianLocalB_full_frame_stabilizer_card :
    Nat.card (MulAction.stabilizer icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalBRoot))=96 := by
  have heq : MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalBRoot)={p : IcosianRootPoint | HasIcosianRootPointShape p 1} := by
    ext p
    exact (icosianLocalB_full_frame_orbit p).symm
  have ho : Nat.card (MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalBRoot))=24 := by
    rw [Nat.card_congr (Equiv.setCongr heq)]
    exact icosianRootPointShape_card 1
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianCoordinateFrameStabilizer (icosianRootToPoint icosianLocalBRoot))
  rw [Nat.card_prod,ho,icosianCoordinateFrameStabilizer_card] at h
  omega

end Atlas.Conway
