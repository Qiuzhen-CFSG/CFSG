module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.ModelProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Transport

/-!
# Incident-core indices and the p.905 pencil assembly

The incident intersection has order at most two modulo the original vertex
two-core. This is proved from the literal binary matrix cores and the actual
source projection. For separation, a finite matrix selection is transported
through that projection and the supplied natural-module isomorphism.

The three selected matrix cores generate the whole quotient. Their full
preimages therefore generate the vertex stabilizer, so the triple fixed
intersection is central there, including its fixed-complement part. The
constructor `flagP905PencilFacts` discharges the matrix selection for the
arbitrary marking supplied by `CommonFacts.natural`.

Source: Meierfrankenfeld--Stellmacher (1993), the symmetry paragraph in the
proof of (4.6.8), printed p.905.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Incident local cores have order at most two modulo the original vertex core. -/
theorem flagP905_intersection_index (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    (Q R (alpha R)).relIndex
      (flagKernel source i ⊓ localFlagKernel source (!i) d) ≤ 2 := by
  rw [Pencils.intersection_index_eq_matrix_card]
  apply Pencils.matrix_intersection_card
  simpa only [map_one] using (Pencils.flagIncident_iff_matrix source i 1 d).mp hd

/-- Source assembly for any supplied literal finite matrix selection. -/
theorem flagP905PencilFacts_of_matrixSeparation (source : LocalSource L R)
    (natural : NaturalU R source.projection) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hmat : Pencils.MatrixSeparation natural.marking source.flag i) :
    FlagP905PencilFacts source i where
  intersection_index := flagP905_intersection_index source i
  separate := Pencils.separate_of_matrixSeparation source natural i hkernel hmat

/-- The finite pencil facts used in MS93 (4.6.8), p.905, follow from the
source projection and its marked natural module. Neither distance four nor
the early distance-four facts are needed for this local incidence argument. -/
theorem flagP905PencilFacts (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    FlagP905PencilFacts source i :=
  flagP905PencilFacts_of_matrixSeparation source common.natural i hkernel
    (Pencils.matrixSeparation common.natural.marking source.flag i)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
