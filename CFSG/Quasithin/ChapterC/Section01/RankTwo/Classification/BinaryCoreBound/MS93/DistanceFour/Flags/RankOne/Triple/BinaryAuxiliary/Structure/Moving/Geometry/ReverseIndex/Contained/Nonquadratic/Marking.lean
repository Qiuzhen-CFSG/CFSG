module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Model

/-!
# The compatible parabolic marking needed by the source calculation

A marking identifies the actual opposite actor modulo Q_alpha with S4.
It retains the original SL3(2) projection, the embedded actor, the kernel,
and both core images. Construction of this marking is a separate finite
geometry obligation; no existence is asserted in this interface.

Source: Meierfrankenfeld--Stellmacher (1993), local flag setup on p.905
and the two parabolic cores used in (4.6.8), pp.906--907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
universe u
variable {M : Type u} [Group M] {L R : Subgroup M}

/-- Restrict the original source projection to either marked parabolic. -/
def modelProjection (source : LocalSource L R) (j : Bool) :
    parabolic source.projection source.flag j →* modelParabolic source.flag j :=
  (source.projection.comp (parabolic source.projection source.flag j).subtype).codRestrict
    (modelParabolic source.flag j) (fun x => x.property)

/-- Compatibility with the original SL3(2) quotient, including the actual
isomorphism from its opposite parabolic. -/
def CompatibleProjection (source : LocalSource L R) (i : Bool) (d : M)
    (π : localFlagActor source (!i) d →* S4Model.Actor) : Prop :=
  ∃ e : modelParabolic source.flag (!i) ≃* S4Model.Actor,
    ∀ (m : parabolic source.projection source.flag (!i))
      (a : localFlagActor source (!i) d),
      (a : FreeAmalgam R) = embedM R (d * (m : M) * d⁻¹) →
      π a = e (modelProjection source (!i) m)

/-- An actual, simultaneous marking of the local actor and its two cores.
The compatibility field requires the same original source projection. -/
structure ParabolicMarking (source : LocalSource L R) (i : Bool) (d : M) where
  hom : localFlagActor source (!i) d →* S4Model.Actor
  onto : Function.Surjective hom
  kernel : hom.ker = (Q R (alpha R)).subgroupOf (localFlagActor source (!i) d)
  compatible : CompatibleProjection source i d hom
  first_le : flagKernel source i ≤ localFlagActor source (!i) d
  first_image : ((flagKernel source i).subgroupOf (localFlagActor source (!i) d)).map hom =
    S4Model.firstCore
  opposite_image :
    ((localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d)).map hom =
      S4Model.oppositeCore

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
