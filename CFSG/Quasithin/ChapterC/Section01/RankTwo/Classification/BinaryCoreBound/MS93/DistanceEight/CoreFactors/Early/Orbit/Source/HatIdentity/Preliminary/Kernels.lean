module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels.Second
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels.Rechoice

/-!
# Assembly of the two D kernel containments from geometric rechoice

Claim (2), including its intersection and edge-centralizer argument, is
proved in Kernels.Second. The genuine source-path rechoice for claim (1)
is still explicit. Once its producer is supplied, the theorem below gives
exactly the published KernelContainmentsOnPath record consumed by
Preliminary.estimatesOnPath_of_calculations. It does not assert an
unconditional producer for that record.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), p.897.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The exact published containment record follows from the single remaining
geometric rechoice producer. Claim (2)'s intersections and detection are discharged. -/
theorem kernelContainmentsOnPath_of_rechoices
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (rechoices : RechoicesOnPath R p) :
    KernelContainmentsOnPath R p := by
  constructor
  · intro i hi hi4 hi6 hne seed
    have hfour := span_le_four_of_rechoices common earlier (rechoices.forward i hi hi4 hi6 hne seed)
    exact ⟨hfour, forward_six_of_four common earlier p hi hi4 hi6 seed hfour⟩
  · intro i hi hi8 hi10 hne seed
    have hfour := span_le_four_of_rechoices common earlier (rechoices.backward i hi hi8 hi10 hne seed)
    exact ⟨hfour, backward_six_of_four common earlier p hi hi8 hi10 seed hfour⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
