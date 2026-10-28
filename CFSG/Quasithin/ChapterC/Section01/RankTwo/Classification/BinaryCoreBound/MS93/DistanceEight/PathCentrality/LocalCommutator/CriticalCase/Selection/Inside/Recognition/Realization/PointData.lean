module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Action

/-!
# The source point retained in natural coordinates

This data specifies coordinates on the earlier natural subgroup U_c, an
actual lift of xD_c to U_c, and the identification of the literal relative
normalizer with its marked point stabilizer. It is input to realization,
not an assertion that such data exist. The lift equality uses the genuine
quotient G_c/D_c and does not require a natural section of the local span.

Source: MS93 (4.4.1)(2), printed p.891, and (1.6), pp.845–847.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- A marking of the original quotient point, with its literal normalizer. -/
structure LocalPointMarking (source : LocalSource L R) (c : Vertex R)
    (hc : color R c = false) (x : stabilizer R c) where
  naturalU : RankOnePairing.NaturalFactor (localProjection source c hc) ⊤
    ((U R c).subgroupOf (stabilizer R c)) ⊥
  lift : (U R c).subgroupOf (stabilizer R c)
  quotient_eq :
    letI := PathCentrality.fixedCore_normal R c
    QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c))
      (lift : stabilizer R c) =
    QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c)) x
  nonzero : (naturalU.coordinates lift).toAdd ≠ 0
  normalizer : ∀ g : stabilizer R c,
    (g : FreeAmalgam R) ∈ pointNormalizer c x ↔
      localProjection source c hc g ∈
        markedPointStabilizer naturalU.marking (naturalU.coordinates lift).toAdd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
