module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Calculations

/-!
# Independent inputs to the preliminary D calculation

The natural-section argument supplies the literal ordered product with D₀.
The kernel argument can use the ensuing seed and span commutator estimates.
It must still prove both numbered containments, including the conjugation
rechoice in the first. These contracts are independent proof obligations;
neither has a producer from the preceding source hypotheses in this module.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
variable {M : Type*} [Group M]

/-- The natural decomposition and its two algebraic commutator consequences. -/
structure SeedEstimates (R : Subgroup M) (a b t : Vertex R) where
  decomposition_product : (hatV R b a : Set (FreeAmalgam R)) =
    (Vcirc R b : Set (FreeAmalgam R)) * (fixedSeed R b : Set (FreeAmalgam R))
  seed_commutator : ⁅fixedSeed R b, stabilizer R b⁆ ≤ H R b
  span_commutator : ⁅normalizerSpan R a b t, Q R a⁆ ≤ H R b

/-- The four natural-section decompositions on the actual supplied path. -/
structure DecompositionsOnPath (R : Subgroup M) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 6 →
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    (hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) : Set (FreeAmalgam R)) =
      (Vcirc R (p.walk.getVert (i - 2)) : Set (FreeAmalgam R)) *
        (fixedSeed R (p.walk.getVert (i - 2)) : Set (FreeAmalgam R))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 10 →
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    (hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) : Set (FreeAmalgam R)) =
      (Vcirc R (p.walk.getVert (i + 2)) : Set (FreeAmalgam R)) *
        (fixedSeed R (p.walk.getVert (i + 2)) : Set (FreeAmalgam R))

/-- The first two numbered containments, conditional on the preceding seed
calculation. The producer must handle the relative-normalizer rechoice. -/
structure KernelContainmentsOnPath (R : Subgroup M) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 4 ≤ i → i ≤ 6 →
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) →
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 4)) ∧
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ≤ Q R (p.walk.getVert (i + 6))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 10 →
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    SeedEstimates R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) →
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 4)) ∧
    normalizerSpan R (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ≤ Q R (p.walk.getVert (i - 6))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary
