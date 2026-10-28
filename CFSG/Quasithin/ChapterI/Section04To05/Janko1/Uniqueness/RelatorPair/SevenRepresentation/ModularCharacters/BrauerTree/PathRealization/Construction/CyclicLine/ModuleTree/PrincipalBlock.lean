module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock

/-!
# The principal eleven-block and its Sylow Brauer correspondent

For the explicit ordinary-block identification and the supplied compatible
roots, the literal reduced projector over `ElevenClosure` is the primitive
principal block. Its coefficient restriction to the centralizer of a Sylow
eleven-subgroup is the primitive local principal block. Together with maximal
Brauer support this supplies the block identification needed by cyclic
incidence, with the exact residue map used by the module-tree construction.

Source: Feit III.8--9 and V.6.2, printed pp.209--210.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
open Representation.CyclicDefect.PrimeOrderRealLine
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Primitivity for the projector used by the actual eleven-block modules. -/
public theorem principalBlock_reduced_isCentrallyPrimitive
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960) :
    ModularBlock.IsCentrallyPrimitive (reducedPrincipal b.data r.residue) :=
  reducedPrincipal_isCentrallyPrimitive b.data r.residue

/-- The Sylow Brauer image is the actual primitive local principal block. -/
public theorem principalBlock_sylowBrauer_isCentrallyPrimitive
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (P : Sylow 11 G) :
    ModularBlock.IsCentrallyPrimitive
      (ModularBlock.DefectSupport.subgroupCentralizerRestriction ElevenClosure
        (P : Subgroup G) (reducedPrincipal b.data r.residue)) :=
  reducedPrincipal_sylowBrauer_isCentrallyPrimitive b.data r.residue P

/-- The primitive block's defect group is the supplied Sylow eleven-subgroup. -/
public theorem principalBlock_primitive_sylow_defect
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (P : Sylow 11 G) :
    ModularBlock.IsCentrallyPrimitive (reducedPrincipal b.data r.residue) ∧
      Maximal (HasBrauerSupport 11 (reducedPrincipal b.data r.residue)) (P : Subgroup G) :=
  ⟨principalBlock_reduced_isCentrallyPrimitive b r,
    sylow_maximal_brauerSupport b.data r.residue P⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
