module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.ComparisonData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Central
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Factors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison.Pencil

/-!
# The midpoint comparison in MS93 (4.6.8)

The source escape selects an incident midpoint flag for the original X.
Containment of Z_alpha in the second layers at escaping flags gives the
full first-actor action bound by the three-core pencil. Comparing the two
actual natural X factors then gives the opposite-core containment, mutual
commutator bound, and central inclusion required by `MiddleComparison`.

`Comparison.Central` proves the central-layer containment at every escaping
flag from the supplied natural section and moving and X factors, using the
actual marked actions and the D > U argument. `middleComparison` combines
that result with the conditional constructor, choosing an actual midpoint
transporter and discharging every intermediate containment premise.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final paragraphs of printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- All comparison fields follow once the preceding source central-layer
containments have been established. Final source assembly must discharge
this extra premise. -/
theorem middleComparison_of_center_containments
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (hcenter : ∀ e : M, flagIncident source i 1 e →
      ¬ X source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom →
      Z R (alpha R) ≤ (secondFlagLayer source i e).map t.conjugation.toMonoidHom) :
    Nonempty (MiddleComparison source geometry i p) := by
  obtain ⟨e, he, hc⟩ := exists_middle_X_crossing source geometry hb early i hkernel p t x
  obtain ⟨hcore, hcomm, hZX⟩ := middle_X_pair_of_center_le_second source geometry
    (by omega) early i hkernel p t moving x e he hc (hcenter e he hc)
  exact ⟨⟨t, e, he, hc,
    middle_center_action_of_containments source geometry hb early i hkernel p t x hcenter,
    hcore, hcomm, hZX⟩⟩

/-- The genuine midpoint comparison from the source preparatory configuration
and the marked natural factors. Central-layer containment holds at every
escaping flag, giving the full first-actor action bound as well as the
comparison of the selected original and transported X factors. -/
theorem middleComparison
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0) :
    Nonempty (MiddleComparison source geometry i p) := by
  let t := middleTransport p
  exact middleComparison_of_center_containments source geometry hb early i hkernel p t moving x
    (middle_center_le_second_of_X_crossing source geometry common hb early i hkernel
      natural p t moving x)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
