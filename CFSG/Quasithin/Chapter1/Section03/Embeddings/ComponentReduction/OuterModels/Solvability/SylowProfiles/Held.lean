module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowSource
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations

/-!
# Full Held outer solvability from the actual Sylow profile

The intrinsic order-four profile proves that the automorphism group of the
fixed Held two-subgroup is a two-group, hence solvable. Its proved two-group
and normalizer properties identify it with an actual Sylow subgroup. The
finite-simple S₂ fixer theorem and Sylow restriction then give full outer
solvability. Simplicity is inherited from the matching Theorem C branch.

This discharges the Held local automorphism input of the full-solvability
route for Aschbacher--Smith A.3.9, pp.45--46. The original Xi restrictions
and stronger automorphism-realization contracts remain separate results.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

/-- The Held branch of full outer solvability, with simplicity inherited
from the actual source consumer and no local profile premise remaining. -/
public theorem held_outer_isSolvable_of_frattini_profile [IsSimpleGroup Held.He] :
    Group.IsSolvable (MulAut.Outer Held.He) := by
  obtain ⟨P, hP⟩ := Held.LocalPairs.SylowGeometry.Calculations.exists_representative_sylow
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq
  let : Group.IsSolvable (MulAut P) := by
    rw [hP]
    exact Held.SylowAutomorphismSolvability.representative_mulAut_isSolvable
  exact simple_outer_isSolvable_of_sylowAut P

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
