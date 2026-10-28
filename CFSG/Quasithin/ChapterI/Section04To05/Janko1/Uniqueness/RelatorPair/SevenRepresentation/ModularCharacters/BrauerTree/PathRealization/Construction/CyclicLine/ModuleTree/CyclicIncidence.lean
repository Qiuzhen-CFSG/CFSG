module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation

/-!
# Local source inputs for the principal eleven-block incidence theorem

The inertia group is the actual stabilizer of the local Brauer projector,
not a name for a group index. Its equality with the Sylow normalizer gives
inertial index ten. The order, cyclicity, ordinary row count and regular
root orders come from the already established source-group data. Only the
two modular primitivity statements remain explicit in the input constructor.

This supplies the local inputs of Feit VII.1 and VII.2.11. The simple count,
cyclic column norms and matrix indecomposability remain source obligations
before the final assertion `n = 10 ∧ Nonempty (Incidence a)` can be assembled.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The literal local projector has the entire Sylow normalizer as its inertia group. -/
public theorem principalBlock_local_inertia (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960) (P : Sylow 11 G) :
    localBlockInertia (P : Subgroup G)
      (DefectSupport.subgroupCentralizerRestriction ElevenClosure (P : Subgroup G)
        (reducedPrincipal b.data r.residue)) = Subgroup.normalizer (P : Set G) :=
  reducedPrincipal_inertia b.data r.residue (P : Subgroup G)

/-- The actual block stabilizer, not just the group normalizer, has index ten. -/
public theorem principalBlock_local_inertialIndex (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    localInertialIndex (P : Subgroup G)
      (DefectSupport.subgroupCentralizerRestriction ElevenClosure (P : Subgroup G)
        (reducedPrincipal b.data r.residue)) = 10 := by
  rw [reducedPrincipal_inertialIndex]
  exact sylow_eleven_centralizer_index d horder P

/-- Discharge all local group and root inputs from the literal source-group
facts, retaining precisely the two independently supplied primitivity premises. -/
public theorem principalBlock_cyclicInput (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560) (P : Sylow 11 G)
    (hprincipal : IsCentrallyPrimitive (reducedPrincipal b.data r.residue))
    (hlocal : IsCentrallyPrimitive
      (DefectSupport.subgroupCentralizerRestriction ElevenClosure (P : Subgroup G)
        (reducedPrincipal b.data r.residue))) :
    PrimeOrderInput b.data r.residue 15960 P where
  sylow_card := sylow_eleven_card horder P
  cyclic := sylow_eleven_isCyclic horder P
  principal_primitive := hprincipal
  local_primitive := hlocal
  inertial_index := principalBlock_local_inertialIndex b r horder P
  ordinary_card := principalBlock_card b
  regular_orders := regular_order_dvd_root_order horder

/-- The exceptional-multiplicity expression for the actual local block is one. -/
public theorem principalBlock_inertial_multiplicity_quotient
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    (Nat.card P - 1) / localInertialIndex (P : Subgroup G)
      (DefectSupport.subgroupCentralizerRestriction ElevenClosure (P : Subgroup G)
        (reducedPrincipal b.data r.residue)) = 1 := by
  rw [sylow_eleven_card horder P, principalBlock_local_inertialIndex b r horder P]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
