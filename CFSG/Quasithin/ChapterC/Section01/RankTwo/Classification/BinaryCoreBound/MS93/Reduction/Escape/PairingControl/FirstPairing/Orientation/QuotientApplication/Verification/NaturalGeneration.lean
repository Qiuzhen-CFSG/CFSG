module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Model.Construction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Transport

/-!
# Natural generation in the first quotient application

`SelectedSeed.moving_le_generated` proves the moving-image containment.
`SelectedSeed.rankOneFactor_nonempty` constructs the natural two-space on
the actual opposite local closure, acted on by the untilded local residual.
The selected element has a nonzero coordinate fixed by the first parabolic.
Its opposite-parabolic orbit spans a natural plane; transporting those
coordinates to the local closure and identifying the intrinsic kernel
with the fixed preimage C completes the rank-one factor.

Both conclusions take the selected seed explicitly and feed the remaining
pairing-premise assembly in `QuotientApplication.Verification`.
Source: Meierfrankenfeld--Stellmacher (1993), (1.7), printed pp.847--848,
and its first quotient application on p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

namespace SelectedSeed

/-- The actual opposite local closure modulo its intrinsic C-kernel is a
natural binary two-space for the untilded local residual. -/
theorem rankOneFactor_nonempty (s : SelectedSeed geometry a f)
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (ha : color R a = false) :
    Nonempty (RankOneFactor
      (localResidual (parabolic (projection f) s.flag (!s.side)))
      (localGenerated (parabolic (projection f) s.flag (!s.side)) s.X) s.C) := by
  let d := s.naturalSeedData source hb ha
  obtain ⟨c⟩ := planeCoordinates_nonempty d.natural.marking s.flag s.side
    d.vector d.nonzero d.fixed
  obtain ⟨n⟩ := d.rankOneFactor_nonempty c
  exact ⟨{ n with kernel :=
    n.kernel.trans (s.C_subgroupOf_localGenerated source hb ha).symm }⟩

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
