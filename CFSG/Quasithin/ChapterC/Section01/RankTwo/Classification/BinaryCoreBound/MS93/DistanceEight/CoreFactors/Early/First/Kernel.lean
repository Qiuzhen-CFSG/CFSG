module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Calculations
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Product
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection

/-!
# The first kernel calculation on the source path

Apply the local quotient reduction at the three forward and three backward
centers of the supplied source path. The endpoint actions are genuinely local
in each case, and the quotient retains the exact B-subgroup and quotient map.

The product calculation bounds the endpoint commutator using the radius-four
contradiction. The detection calculation uses the genuine natural section
from Earlier to identify the fixed subgroup. Together they discharge the
premises of the quotient reduction in `kernelFactsOnPath`. SourcePath
existence remains a separate obligation of Early.First; the path is an
explicit input to this theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(ii)--(iii), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
variable {M : Type*} [Group M]
variable [Finite M] {R L : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

/-- All six kernel calculations, once the two remaining source implications
are supplied. This is conditional assembly, not their source proof. -/
theorem kernelFactsOnPath_of_product_and_detection
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (product : ProductBoundsOnPath R p)
    (detection : FixedPointDetectionOnPath R geometry p) :
    KernelFactsOnPath R geometry p := by
  constructor
  · intro i hi hi2 hi6
    have hf : Even (i + 8) := hi.add (by decide : Even 8)
    apply Kernel.calculation_of_product_and_detection common
      (p.even_color hi (by omega)) (p.even_color hf (by omega))
      (Kernel.endpoint_local earlier p hi (by omega) hf (by omega) (by omega) (by omega)).1
      (product.forward i hi hi2 hi6)
    exact detection.forward i hi hi2 hi6 (product.forward i hi hi2 hi6)
  · intro i hi hi8 hi12
    have hf : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
    apply Kernel.calculation_of_product_and_detection common
      (p.even_color hi (by omega)) (p.even_color hf (by omega))
      (Kernel.endpoint_local earlier p hf (by omega) hi (by omega) (by omega) (by omega)).2
      (product.backward i hi hi8 hi12)
    exact detection.backward i hi hi8 hi12 (product.backward i hi hi8 hi12)

/-- MS93 (4.5.1)(ii)--(iii) at the three forward and three backward centers.
The literal product bound, relative B-normality, B-containment and quotient
centralizer equality require no further calculation premises. -/
theorem kernelFactsOnPath (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : KernelFactsOnPath R geometry p :=
  kernelFactsOnPath_of_product_and_detection common earlier p
    (Kernel.Product.productBoundsOnPath source common earlier p)
    (Kernel.fixedPointDetectionOnPath common earlier p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
