module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Spans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ModelProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ResidualGeneration

/-!
# Assembly of the literal quotient-geometry bridge

Ambient dual action, faithful natural coordinates on Z, and the exact
coordinate images of local normal closures lift the finite matrix pencil
to every field of the published `DualPencil` interface. Opposite actors
retain their parabolic factorization, so their seed containments hold
before passing to the quotient.

The zero residual fixed-space hypothesis selects the proved marked matrix
pencil. The opposite local two-core normally generates a subgroup of odd
index in the actual local normalizer, so its normal closure contains the
untilded residual. Thus `of_dual` discharges every geometric premise, and
`of_natural` first constructs the contragredient coordinates from the
source's natural quotient. Both retain only the source branch hypotheses
and the independently supplied `LocalFacts`; the subsequent incidence
argument gives the elementwise commutator conclusion of (1.7)(ii).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7)(ii), printed p.848.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

/-- The complete ambient pencil follows from the finite matrix calculation
and the separate local residual-generation theorem. -/
theorem of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i)
    (hres : localResidual (localParabolic e i) ≤
      localGenerated (localParabolic e i) (localCore (localParabolic e (!i)))) :
    DualPencil e i Z W X where
  seed_bound := seed_bound_of_matrixGeometry d f g
  star_cover := star_cover_of_matrixGeometry d f n g
  star_neighbors := star_neighbors_of_matrixGeometry d f n g
  opposite_cover := opposite_cover_of_matrixGeometry d f n g
  core_fixed := core_fixed_of_matrixGeometry d f n g
  residual_generation := hres
  local_irreducible := local_irreducible_of_matrixGeometry d f g

/-- The dual pencil from the source's zero residual fixed space and the
specified contragredient quotient, with all matrix and generation premises
discharged. The local groups and the pairing kernel are the literal ones. -/
theorem of_dual (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    DualPencil e i Z W X :=
  of_matrixGeometry d f n
    (matrixGeometry_of_no_fixed d.natural.marking e.flag i (model_fixed_eq_bot d f h))
    (residual_generation f i)

/-- The dual pencil directly from the natural quotient assumed in MS93
(1.7)(ii). The compatible dual coordinates are constructed, not assumed. -/
theorem of_natural (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    DualPencil e i Z W X :=
  of_dual d f (Duality.contragredient d n f.component_image f.z_central h) h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
