module

public import Theory.Representation.FirstCohomologyG2Natural.OctonionCocycle
public import Theory.Representation.FirstCohomologyG2Natural.BinaryBound
public import Theory.Representation.FirstCohomologyG2Natural.NonbinaryBound

/-!
# First cohomology of the natural G₂ derived action: reduction to spanning

The trace-one octonion supplies a proved nonprincipal cocycle. This module
reduces the dimension-one conclusion to surjectivity of octonion displacement,
or to the seven-dimensional upper bound for all cocycles. The lower bound and
the dimension of the constructed cocycle subspace are unconditional.

The family-specific upper bounds are imported from the binary and nonbinary
calculation modules below; the final case split is assembled here for the
actual derived group, including the field of order two.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(5), printed p.408 / PDF p.419, citing Jones--Parshall (1976).
-/

@[expose] public section

namespace Atlas.G2.Natural
open Atlas.SplitOctonion Representation.OneCohomology
variable (K : Type*) [Field K] [CharP K 2]

/-- Surjectivity of octonion displacement gives the required cocycle normal form. -/
theorem cyclicNormalForm_of_ambientCocycle_surjective
    (h : Function.Surjective (ambientCocycle K)) :
    ∀ f : cocycles (derivedAction K), ∃ a : K, ∃ v : Space K,
      f = a • distinguishedCocycle K + principal (derivedAction K) v := by
  intro f
  obtain ⟨x, rfl⟩ := h f
  exact ⟨trace x, mk K (traceZeroPart K x), ambientCocycle_decomposition K x⟩

/-- The dimension-one calculation, conditional on the remaining spanning assertion. -/
theorem finrank_H1_eq_one_of_ambientCocycle_surjective
    (h : Function.Surjective (ambientCocycle K)) :
    Module.finrank K (H1 (derivedAction K)) = 1 :=
  finrank_H1_of_cyclicNormalForm (derivedAction K) (distinguishedCocycle K)
    (distinguishedCocycle_nonprincipal K) (cyclicNormalForm_of_ambientCocycle_surjective K h)

/-- The only remaining numerical input is an upper bound proved from the cocycle equations. -/
theorem finrank_H1_eq_one_of_finrank_cocycles_le [Finite K]
    (h : Module.finrank K (cocycles (derivedAction K)) ≤ 7) :
    Module.finrank K (H1 (derivedAction K)) = 1 :=
  finrank_H1_eq_one_of_ambientCocycle_surjective K
    (ambientCocycle_surjective_of_finrank_cocycles_le K h)

/-- The natural six-dimensional module of the actual derived G₂ group has
first cohomology of dimension one over every finite characteristic-two field.

The binary branch uses the explicit pair generation theorem for the actual
`G₂(2)'`; the other branch uses the torus/root cocycle calculation. -/
public theorem finrank_H1_eq_one [Finite K] :
    Module.finrank K (H1 (derivedAction K)) = 1 := by
  by_cases h : Nat.card K = 2
  · exact finrank_H1_eq_one_of_finrank_cocycles_le K
      (finrank_cocycles_le_seven_binary K h)
  · exact finrank_H1_eq_one_of_finrank_cocycles_le K
      (finrank_cocycles_le_seven_nonbinary K (by
        have hc := Finite.one_lt_card (α := K)
        omega))

end Atlas.G2.Natural
