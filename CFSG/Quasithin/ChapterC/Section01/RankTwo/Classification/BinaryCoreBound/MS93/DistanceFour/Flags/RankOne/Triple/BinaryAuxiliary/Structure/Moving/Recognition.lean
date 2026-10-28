module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.Bridge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.LinearReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.Reflection

/-!
# Recognition of the actual binary auxiliary moving factor

The source displacement estimates construct a small reflection on the genuine
quotient Y/U. The binary S3 calculation bounds its full moving subspace by
four, and nontrivial two-residual action makes that subspace a natural plane.
The coordinate lift retains surjectivity, the exact denominator U, the exact
full-actor kernel Q inside P, and the literal ambient conjugation action.
The whole quotient Y/U may retain a central summand.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving

universe u

/-- Source-to-coordinate assembly with the pure representation bound explicit. -/
theorem movingFactor_of_smallDisplacement_of_bound
    {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) (E : Subgroup (FreeAmalgam R))
    (estimates : SmallDisplacementData source i d E) (bound : SmallReflectionBound.{u}) :
    Nonempty (MovingFactor source i d) := by
  let b := auxiliaryModule source geometry common early i d
  obtain ⟨π, hπ, hk, ρ, ha⟩ := b.exists_descendedRepresentation estimates.core
  have hm := b.descended_residual_moves π ρ ha estimates.residual
  obtain ⟨t, ht, htn, hsmall⟩ := b.exists_small_reflection estimates π hk ρ ha
  obtain ⟨n⟩ := naturalMoving_of_card ρ hm (bound ρ t ht htn hsmall)
  exact b.movingFactor_of_naturalMoving geometry common.large_distance π hπ hk ρ ha n

/-- The binary source estimates recognize the actual factor ([Y,P] sup U)/U
as the natural SL2(2) plane. The full actor map has exactly the original kernel
Q inside P, and the onto coordinates have exactly the denominator U. -/
theorem movingFactor_of_smallDisplacement
    {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) (E : Subgroup (FreeAmalgam R))
    (estimates : SmallDisplacementData source i d E) :
    Nonempty (MovingFactor source i d) :=
  movingFactor_of_smallDisplacement_of_bound source geometry common early i d E estimates
    smallReflectionBound

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
