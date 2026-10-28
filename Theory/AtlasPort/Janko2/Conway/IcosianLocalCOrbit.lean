/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalCOrbit.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalCStabilizerBound
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# IcosianLocalCOrbit

The shape-C root points form one full frame-stabilizer orbit. A stabilizer bound and
the known shape count force orbit exhaustion and exact orders.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalCOrbit.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

@[instance_reducible]
def icosianLiftedRootPointAction : MulAction icosianLiftedMonomial IcosianRootPoint :=
  MulAction.compHom IcosianRootPoint icosianMonomialToHermitian
attribute [local instance] icosianLiftedRootPointAction

def icosianLocalCOrbitToShape
    (p : MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot)) :
    IcosianRootPointShape 2 := by
  refine ⟨p.val,?_⟩
  obtain ⟨g,hg⟩ := p.property
  refine ⟨icosianMonomialToHermitian g • icosianLocalCRoot,?_,
    (icosianMonomialRoot_shape g icosianLocalCRoot 2).mpr icosianLocalCRoot_shape⟩
  have h := congrArg Subtype.val hg
  exact (icosianRootPoint_smul _ _).trans h

theorem icosianLocalCOrbitToShape_injective : Function.Injective icosianLocalCOrbitToShape := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : IcosianRootPointShape 2 => z.val) h

def icosianLocalCStabilizerEquiv :
    MulAction.stabilizer icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot) ≃
      icosianLocalCStabilizer :=
  Equiv.subtypeEquivRight (fun g => by
    change (icosianMonomialToHermitian g • icosianRootToPoint icosianLocalCRoot=
      icosianRootToPoint icosianLocalCRoot) ↔
      icosianMonomialToHermitian g • icosianRootPoint icosianLocalCRoot=
        icosianRootPoint icosianLocalCRoot
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩)

theorem icosianLocalCOrbit_card :
    Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot))=192 := by
  have hl := Nat.card_le_card_of_injective icosianLocalCOrbitToShape
    icosianLocalCOrbitToShape_injective
  rw [icosianRootPointShape_card] at hl
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalCStabilizerEquiv,icosianLiftedMonomial_card] at he
  have hb := icosianLocalCStabilizer_card_le
  change Nat.card (MulAction.orbit icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot))≤192 at hl
  nlinarith

theorem icosianLocalCStabilizer_card : Nat.card icosianLocalCStabilizer=12 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianLiftedMonomial (icosianRootToPoint icosianLocalCRoot))
  rw [Nat.card_prod,Nat.card_congr icosianLocalCStabilizerEquiv,
    icosianLiftedMonomial_card,icosianLocalCOrbit_card] at he
  omega

/-- The full actual monomial group is transitive on the192 C-type root lines.
This follows from the scalar stabilizer bound and the independently counted family. -/
theorem icosianLocalCOrbit_exhaustive (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 2 ↔
      ∃ g : icosianLiftedMonomial,icosianMonomialToHermitian g •
        icosianRootToPoint icosianLocalCRoot=p := by
  have hs : Function.Surjective icosianLocalCOrbitToShape :=
    ((Nat.bijective_iff_injective_and_card icosianLocalCOrbitToShape).mpr
      ⟨icosianLocalCOrbitToShape_injective,by
        rw [icosianLocalCOrbit_card,icosianRootPointShape_card]; rfl⟩).2
  constructor
  · intro hp
    obtain ⟨q,hq⟩ := hs ⟨p,hp⟩
    have he : q.val=p := congrArg Subtype.val hq
    obtain ⟨g,hg⟩ := q.property
    exact ⟨g,hg.trans he⟩
  · rintro ⟨g,rfl⟩
    exact (icosianLocalCOrbitToShape ⟨_,⟨g,rfl⟩⟩).property

theorem icosianLocalC_full_frame_orbit (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 2 ↔
      ∃ g : icosianCoordinateFrameStabilizer,g.val • icosianRootToPoint icosianLocalCRoot=p := by
  constructor
  · intro hp
    obtain ⟨g,hg⟩ := (icosianLocalCOrbit_exhaustive p).mp hp
    exact ⟨⟨icosianMonomialToHermitian g,icosianMonomial_mem_frameStabilizer g⟩,hg⟩
  · rintro ⟨g,rfl⟩
    exact (icosianCoordinateFrame_rootPoint_shape g (icosianRootToPoint icosianLocalCRoot) 2).mpr
      ⟨icosianLocalCRoot,rfl,icosianLocalCRoot_shape⟩

theorem icosianLocalC_full_frame_stabilizer_card :
    Nat.card (MulAction.stabilizer icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalCRoot))=12 := by
  have heq : MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalCRoot)={p : IcosianRootPoint | HasIcosianRootPointShape p 2} := by
    ext p
    exact (icosianLocalC_full_frame_orbit p).symm
  have ho : Nat.card (MulAction.orbit icosianCoordinateFrameStabilizer
      (icosianRootToPoint icosianLocalCRoot))=192 := by
    rw [Nat.card_congr (Equiv.setCongr heq)]
    exact icosianRootPointShape_card 2
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianCoordinateFrameStabilizer (icosianRootToPoint icosianLocalCRoot))
  rw [Nat.card_prod,ho,icosianCoordinateFrameStabilizer_card] at h
  omega

end Atlas.Conway
