module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.BinaryPencil
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.Residuals
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction

/-!
# Assembly of the fixed local pencil in MS93 (1.7)

The nonzero residual fixed space selects the point member of the arbitrarily
marked parabolic pair. Its value line and the neighboring fixed plane give
the commutator bounds and two actors in the actual neighboring normalizer.
The binary rank-one quotient then supplies a seed generator and both
neighboring decompositions. The untilded local residual normally generates
the entire extension, supplying the remaining component containment.

`of_fixed` constructs every field of `FixedPencil` from the source data,
the independently supplied local-structure facts, and the fixed-case
hypothesis. It does not construct `LocalFacts` or assert the later
centralizer-propagation conclusions of (1.7)(i).
Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), printed p.847.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
open Subgroup
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

/-- Every fixed-pencil field follows from the local value-space geometry. -/
theorem of_valueGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (v : ValueGeometry e i Z W X) : FixedPencil e i Z W X := by
  obtain ⟨hseed, hneighbors⟩ := seed_and_neighbors d f v
  refine ⟨v.seed_bound, v.local_bound, v.local_proper, v.seed_fixed,
    v.seed_card, hseed, hneighbors, ?_⟩
  rw [residual_normalClosure_eq_top e f i]
  exact le_top

/-- The complete fixed-case pencil from the source data and local structure,
with no extra geometric or centralizer-propagation hypotheses. -/
theorem of_fixed (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥) :
    FixedPencil e i Z W X :=
  of_valueGeometry d f (ValueConstruction.of_fixed d f h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
