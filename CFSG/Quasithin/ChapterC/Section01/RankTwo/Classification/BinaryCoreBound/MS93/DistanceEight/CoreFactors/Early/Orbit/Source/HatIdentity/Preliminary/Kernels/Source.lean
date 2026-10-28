module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.PathExtension.Rechoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary

/-!
# Both source D kernel containments

The actual relative-normalizer rechoice proves the first containment; the
checked moving-chain intersection and edge-centralizer argument proves the
second. This removes the geometric-rechoice premise from the preliminary
source calculation. The fixed-seed decomposition and the third containment
are independent remaining source calculations, and are not asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), claims (1)--(2), p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Both numbered kernel containments on the original supplied source path. -/
theorem kernelContainmentsOnPath
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : KernelContainmentsOnPath R p :=
  kernelContainmentsOnPath_of_rechoices common earlier p
    (PathExtension.rechoicesOnPath common earlier p)

/-- Literal preliminary consumer: only the independent fixed-seed decomposition
remains; no rechoice or kernel-containment premise is retained. -/
theorem preliminaryEstimatesOnPath_of_decompositions
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (split : DecompositionsOnPath R p) :
    PreliminaryEstimatesOnPath R p :=
  estimatesOnPath_of_calculations common earlier p split
    (kernelContainmentsOnPath common earlier p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Kernels
