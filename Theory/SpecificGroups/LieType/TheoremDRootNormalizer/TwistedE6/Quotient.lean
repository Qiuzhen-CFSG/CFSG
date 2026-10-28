module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Roots
public import Theory.GroupTheory.QuasithinBasic
import Mathlib.Tactic

/-!
# The literal projective fixed root subgroup

Compose the folded additive root homomorphisms with the quotient of the
defining-characteristic subgroup by its own center. The image of the
fourth curve, at the fixed simple node 3, is a two-group. Injectivity of
this quotient curve is retained as an explicit premise of its nontriviality
and two-local-normalizer consequence.

Source: the actual root-normalizer torus obstruction in Aschbacher–Smith
A.2.18, printed p.40, using the central-quotient convention of GLS3 2.2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace TwistedE6.TheoremDRootNormalizer
noncomputable section

/-- The fixed root curve followed by the literal quotient by the residual's center. -/
def projectiveRootHom (m : ℕ) (s : Bool) (i : Fin 4) :
    Multiplicative (FixedField m) →* Model 2 m :=
  (toModel 2 m).comp (foldedRootHom m s i)

/-- All fixed additive parameters at the fourth, diagram-fixed simple root. -/
def rootSubgroup (m : ℕ) : Subgroup (Model 2 m) :=
  (projectiveRootHom m true 3).range

theorem rootSubgroup_isTwoGroup (m : ℕ) : IsPGroup 2 (rootSubgroup m) := by
  have h : IsPGroup 2 (Multiplicative (FixedField m)) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, nsmul_eq_mul, CharP.cast_eq_zero (FixedField m) 2, zero_mul]
  exact h.of_surjective (projectiveRootHom m true 3).rangeRestrict
    (projectiveRootHom m true 3).rangeRestrict_surjective

def rootNormalizer (m : ℕ) : Subgroup (Model 2 m) :=
  Subgroup.normalizer (rootSubgroup m : Set (Model 2 m))

/-- Faithfulness of the actual quotient curve makes this normalizer two-local. -/
theorem rootNormalizer_isTwoLocal (m : ℕ)
    (hi : Function.Injective (projectiveRootHom m true 3)) : IsTwoLocal (rootNormalizer m) := by
  refine ⟨rootSubgroup m, ?_, rootSubgroup_isTwoGroup m, rfl⟩
  intro h
  have hx : projectiveRootHom m true 3 (Multiplicative.ofAdd (1 : FixedField m)) = 1 := by
    have hm : projectiveRootHom m true 3 (Multiplicative.ofAdd (1 : FixedField m)) ∈
        rootSubgroup m := ⟨_, rfl⟩
    simpa [h] using hm
  have he := hi (hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd he)

end
end TwistedE6.TheoremDRootNormalizer
