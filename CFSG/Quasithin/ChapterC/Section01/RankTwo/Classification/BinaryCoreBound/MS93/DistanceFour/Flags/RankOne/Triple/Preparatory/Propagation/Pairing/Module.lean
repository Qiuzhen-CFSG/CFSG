module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Fixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Transport

/-!
# The local module choice in MS93 (4.6.8)(2)

The midpoint supplies a genuine moving line in the split natural section.
Transporting that line selects an actual conjugate seed fixed modulo Z_alpha
by the opposite untilded residual, whose first-parabolic closure has natural
two-space coordinates. The proved denominator identity retains the literal
global fixed preimage modulo U_alpha. The edge displacement of order four
also forces a nonzero opposite fixed subgroup in U_alpha.

`seedModuleData` assembles all three properties with the original embedding,
common flag and quotient marking, including any graph twist. It uses only
the common and early facts, the selected kernel, the seed commutator bound,
and the full single natural section. The final application of (1.7)(i)
belongs to the parent pairing module.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- Construct the actual seed and its natural rank-one factor from the full
single section, retaining the source's global fixed preimage modulo U_alpha. -/
theorem seedModuleData (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hkernel : flagKernel source i = Q R (beta R))
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hs : SingleSection p) : Nonempty (SeedModuleData p) := by
  let d := splitLineData common early p hkernel hseed hs
  obtain ⟨g, hfixed, ⟨hnatural⟩⟩ := d.transport
  refine ⟨{
    conjugator := g
    seed_fixed := ?_
    local_natural := ?_
    fixed_nonzero := opposite_fixed_nonzero common early i hkernel }⟩
  · simpa only [seed_conjugate, pairing_parabolic] using hfixed
  · rw [fixedPreimage_eq_fixedLayer common p hseed g, pairing_parabolic]
    simpa only [seed_conjugate, fixedLayer] using hnatural

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
