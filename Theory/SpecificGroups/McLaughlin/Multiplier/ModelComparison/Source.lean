module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
/-!
# The actual McLaughlin carrier comparison

The checked rational Leech isometries lift both literal permutation generators
under the same 275-point labeling. The proved permutation order lower bound
and the existing order of the Leech stabilizer make this marked embedding
bijective. No model comparison or generator-lift premise remains.
Source: Aschbacher--Smith A.2.19, printed pp.40--41; I.1.4(2), p.408.
-/
public noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier
open ModelComparison Sporadic.LeechRelated.McL
/-- The original permutation carrier is the actual marked Leech triangle stabilizer. -/
def permutationModelEquiv : Carrier ≃* Atlas.Sporadic.McLaughlin.Model :=
  permutationModelEquivOfLifts generatorLifts permutation_order_lower
/-- The comparison retains the original degree-275 action. -/
theorem permutationModelEquiv_apply (g : Carrier) (x : Fin 275) :
    permutationModelEquiv g • markedPointEquiv x = markedPointEquiv (g.val x) :=
  permutationModelEquivOfLifts_apply generatorLifts permutation_order_lower g x
end Theory.SpecificGroups.McLaughlin.Multiplier
