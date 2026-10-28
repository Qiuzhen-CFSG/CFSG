module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Descent

/-!
# The two remaining D calculations and their same-path contracts

These contracts keep the natural-section decomposition and first two
containments separate from the final product containment. The latter takes
the former explicitly, allowing independent proofs without assuming the
hat identity. Both preserve the contrary assumption and every indexed
vertex. HatIdentity assembles the resulting four configurations and uses
the supplied turns to fill the two remaining interior centers.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), pp.897--898.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The preliminary D calculation under the contrary hat-layer assumption.
The vertices b,a,d,e have source offsets -2,0,4,6 and t has offset -1.
These are proof obligations; no constructor from Earlier is asserted here. -/
structure PreliminaryEstimates (R : Subgroup M) (a b t d e : Vertex R) where
  decomposition_product : (hatV R b a : Set (FreeAmalgam R)) =
    (Vcirc R b : Set (FreeAmalgam R)) * (fixedSeed R b : Set (FreeAmalgam R))
  seed_commutator : ⁅fixedSeed R b, stabilizer R b⁆ ≤ H R b
  span_commutator : ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b
  span_le_four : normalizerSpan R a b t ≤ Q R d
  span_le_six : normalizerSpan R a b t ≤ Q R e

/-- The two forward and two reflected D configurations on the supplied path.
Each calculation is requested only under the printed contrary assumption. -/
structure PreliminaryEstimatesOnPath (R : Subgroup M) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 6 →
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    PreliminaryEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) (p.walk.getVert (i + 4)) (p.walk.getVert (i + 6))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 10 →
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    PreliminaryEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) (p.walk.getVert (i - 4)) (p.walk.getVert (i - 6))

/-- The third printed containment, as a conditional source calculation.
Its producer can work independently of the preliminary-estimate producer;
final assembly must construct those estimates before using this field. -/
structure ThirdContainmentOnPath (R : Subgroup M) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 6 →
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    PreliminaryEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) (p.walk.getVert (i + 4)) (p.walk.getVert (i + 6)) →
    (normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) : Set (FreeAmalgam R)) ⊆
        (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
          (Q R (p.walk.getVert (i + 8)) : Set (FreeAmalgam R))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 10 →
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    PreliminaryEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) (p.walk.getVert (i - 4)) (p.walk.getVert (i - 6)) →
    (normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) : Set (FreeAmalgam R)) ⊆
        (Z R (p.walk.getVert i) : Set (FreeAmalgam R)) *
          (Q R (p.walk.getVert (i - 8)) : Set (FreeAmalgam R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity
