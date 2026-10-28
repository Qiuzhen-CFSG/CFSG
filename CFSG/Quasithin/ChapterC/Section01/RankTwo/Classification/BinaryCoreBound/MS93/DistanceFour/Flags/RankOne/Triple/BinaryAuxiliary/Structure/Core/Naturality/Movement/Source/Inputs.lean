module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Inputs

/-!
# Compatible markings for the actual auxiliary action

A marking identifies the full opposite parabolic modulo Q_alpha with the
literal point parabolic of SL₃(2). It retains both cores of the incident
flag: the actor's core maps to the translation group, and the first flag's
core maps to the incident line core. The quotient presentation below is
separate from the incident pencil and its nonvanishing calculation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source

universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- One compatible flag marking, including the two incident cores. -/
structure ParabolicMarking (source : LocalSource L R) (i : Bool) (d : M) where
  hom : localFlagActor source (!i) d →* Actor
  onto : Function.Surjective hom
  kernel : hom.ker = (Q R (alpha R)).subgroupOf (localFlagActor source (!i) d)
  core_image : ((localFlagKernel source (!i) d).subgroupOf
    (localFlagActor source (!i) d)).map hom = modelCore
  incident_image : ((localFlagKernel source i d).subgroupOf
    (localFlagActor source (!i) d)).map hom = incidentCore

/-- Coordinates on Y/Z_alpha with its conjugation action descended along the
same marked quotient. The invariant layer and pencil are not assumed here. -/
structure QuotientModule (source : LocalSource L R) (i : Bool) (d : M)
    (marking : ParabolicMarking source i d) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) Actor Space
  coordinates : Y source i d →* Multiplicative Space
  onto : Function.Surjective coordinates
  kernel : coordinates.ker = (Z R (alpha R)).subgroupOf (Y source i d)
  action : ∀ (g : localFlagActor source (!i) d) (x y : Y source i d),
    (y : FreeAmalgam R) = (g : FreeAmalgam R) * (x : FreeAmalgam R) *
      (g : FreeAmalgam R)⁻¹ →
    (coordinates y).toAdd = representation (marking.hom g) (coordinates x).toAdd

attribute [instance] QuotientModule.addCommGroup QuotientModule.module QuotientModule.finite

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source
