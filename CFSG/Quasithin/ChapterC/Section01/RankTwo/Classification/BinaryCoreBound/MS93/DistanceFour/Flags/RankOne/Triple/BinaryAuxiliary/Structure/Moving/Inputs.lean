module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Quotient

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Midpoint

/-!
# The source estimates needed to recognize the moving auxiliary factor

The full actor quotient is already the marked SL2(2). The geometric
calculation must show that its core fixes Y/U, its two-residual moves Y/U,
and an escaping two-subgroup has displacement of order at most two.
`SmallDisplacementData` records precisely these group-theoretic estimates;
it contains no natural-factor, coordinate or dimension assertion.

The geometric producer and the conditional representation recognition can
be proved independently. The moving-factor assembly must supply both.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Intrinsic action estimates at one actual flag. These are construction
obligations, not additional assumptions of the requested source theorem. -/
structure SmallDisplacementData (source : LocalSource L R) (i : Bool) (d : M)
    (E : Subgroup (FreeAmalgam R)) : Prop where
  actor : E ≤ localFlagActor source (!i) d
  two : IsPGroup 2 E
  escapes : ¬ E ≤ localFlagKernel source (!i) d
  core : ⁅Y source i d, localFlagKernel source (!i) d⁆ ≤ secondFlagLayer source i d
  residual : ¬ ⁅Y source i d, localFlagResidual source (!i) d⁆ ≤ secondFlagLayer source i d
  small : (secondFlagLayer source i d).relIndex ⁅Y source i d, E⁆ ≤ 2


/-- The remaining geometric comparison, together with the action facts needed
for recognition. All subgroups at the midpoint retain the supplied transporter.
There is no natural-factor or coordinate hypothesis. -/
structure MiddleComparisonData (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i)
    (t : MiddleTransport p.middle) where
  flag : M
  incident : flagIncident source i 1 flag
  actor : secondFlagLayer source i p.delta0 ≤
    (localFlagActor source (!i) flag).map t.conjugation.toMonoidHom
  escapes : ¬ secondFlagLayer source i p.delta0 ≤
    (localFlagKernel source (!i) flag).map t.conjugation.toMonoidHom
  comparison : (Z R (alpha R)).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i flag).map t.conjugation.toMonoidHom⁆ ≤
    (Z R p.middle).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (secondFlagLayer source i flag).map t.conjugation.toMonoidHom⁆
  core : ⁅Y source i flag, localFlagKernel source (!i) flag⁆ ≤ secondFlagLayer source i flag
  residual : ¬ ⁅Y source i flag, localFlagResidual source (!i) flag⁆ ≤
    secondFlagLayer source i flag

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
