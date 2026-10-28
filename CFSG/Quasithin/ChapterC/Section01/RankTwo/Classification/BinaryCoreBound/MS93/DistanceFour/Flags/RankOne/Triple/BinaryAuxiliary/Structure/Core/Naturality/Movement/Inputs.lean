module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Inputs
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Models
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The action needed for the nonzero D/core calculation

The abstract pencil uses the literal point parabolic of SL₃(2), its
translation four-group and the incident line four-group. Its seed is fixed
by the incident core and its conjugates span the module. The full core acts
trivially modulo the invariant layer. No nonvanishing conclusion is part
of this interface.

The source action presents Y/Z_alpha, retaining the original full actor,
its quotient marking, U and the full-actor fixed preimage D. Constructing
this presentation and proving the abstract pencil calculation are separate
obligations; neither is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement

abbrev Actor := Matrix.PSL3Two.pointParabolicSL

/-- The actual normal translation four-group in the model actor. -/
abbrev modelCore : Subgroup Actor :=
  Matrix.PSL3Two.MarkedAutomorphisms.pointV.subgroupOf Actor

/-- The incident line core inside the same point actor. -/
abbrev incidentCore : Subgroup Actor :=
  Matrix.PSL3Two.MarkedAutomorphisms.lineV.subgroupOf Actor

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Preimage of the fixed space of the full actor on W/U. -/
def fixedModulo (ρ : Representation (ZMod 2) Actor W) (U : Submodule (ZMod 2) W) :
    Submodule (ZMod 2) W :=
  ⨅ g : Actor, U.comap (ρ g - 1)

theorem mem_fixedModulo (ρ : Representation (ZMod 2) Actor W)
    (U : Submodule (ZMod 2) W) (v : W) :
    v ∈ fixedModulo ρ U ↔ ∀ g, ρ g v - v ∈ U := by
  simp only [fixedModulo, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.sub_apply, Module.End.one_apply]

/-- The incident seed and invariant layer for the binary parabolic calculation. -/
structure Pencil (ρ : Representation (ZMod 2) Actor W) (U : Submodule (ZMod 2) W) where
  seed : Submodule (ZMod 2) W
  invariant : ∀ g : Actor, U ≤ U.comap (ρ g)
  core_displacement : subspaceCommutator ρ ⊤ modelCore ≤ U
  seed_fixed : seed ≤ fixedSpace ρ incidentCore
  generated : (⨆ g : Actor, seed.map (ρ g)) = ⊤

universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- A genuine marked presentation of Y/Z_alpha and its incident pencil.
Every field is a coordinate, action or subgroup identification; in particular
no nonzero displacement or natural X factor is assumed. -/
structure SourceAction (source : LocalSource L R) (i : Bool) (d : M) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) Actor Space
  marking : localFlagActor source (!i) d →* Actor
  marking_onto : Function.Surjective marking
  marking_kernel : marking.ker =
    (Q R (alpha R)).subgroupOf (localFlagActor source (!i) d)
  core_image : ((localFlagKernel source (!i) d).subgroupOf
    (localFlagActor source (!i) d)).map marking = modelCore
  coordinates : Y source i d →* Multiplicative Space
  onto : Function.Surjective coordinates
  kernel : coordinates.ker = (Z R (alpha R)).subgroupOf (Y source i d)
  action : ∀ (g : localFlagActor source (!i) d) (x y : Y source i d),
    (y : FreeAmalgam R) = (g : FreeAmalgam R) * (x : FreeAmalgam R) *
      (g : FreeAmalgam R)⁻¹ →
    (coordinates y).toAdd = representation (marking g) (coordinates x).toAdd
  layer : Submodule (ZMod 2) Space
  pencil : Pencil representation layer
  layer_preimage : ∀ y : Y source i d,
    (coordinates y).toAdd ∈ layer ↔ (y : FreeAmalgam R) ∈ secondFlagLayer source i d
  fixed_preimage : ∀ y : Y source i d,
    (coordinates y).toAdd ∈ fixedModulo representation layer ↔
      (y : FreeAmalgam R) ∈ D source i d

attribute [instance] SourceAction.addCommGroup SourceAction.module SourceAction.finite

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement
