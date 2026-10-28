module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Pencil

/-!
# The genuine source action and incident pencil on Y/Z_alpha

The compatible flag marking identifies the full opposite actor modulo
Q_alpha with the literal point parabolic. The early radius bounds construct
the elementary quotient Y/Z_alpha and descend its actual conjugation action.
The image of the second layer is invariant, the point core displaces into
it, and the incident-core-fixed first layer generates through its full-actor
orbit. Its full-actor fixed preimage modulo the second layer is exactly D.

This constructs the source action without an assumed module shape or a
nonvanishing conclusion. The separate abstract pencil calculation and source
nonvanishing assembly belong to the consumer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal Y/Z_alpha action, with its original quotient marking, full
actor, exact U and D preimages, and actual incident first-layer pencil. -/
theorem coreMovement_sourceAction (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M) :
    Nonempty (CoreMovement.SourceAction source i d) := by
  obtain ⟨marking⟩ := CoreMovement.Source.exists_parabolicMarking source i d
  let b := CoreMovement.Source.quotientModule source geometry common early i d marking
  exact ⟨{
    Space := b.Space
    representation := b.representation
    marking := marking.hom
    marking_onto := marking.onto
    marking_kernel := marking.kernel
    core_image := marking.core_image
    coordinates := b.coordinates
    onto := b.onto
    kernel := b.kernel
    action := b.action
    layer := b.image (secondFlagLayer source i d)
    pencil := b.pencil geometry common early hkernel
    layer_preimage := b.layer_preimage
    fixed_preimage := b.fixed_preimage geometry common.large_distance }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
