module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime

/-!
# Complete model generation for the replacement overgroups

The moved odd-prime theorem completes the model calculation on the literal
component-orbit Sylow join. The assembly transports the C-component and
its two-core quotient into I∨T, inherits SQTK from the maximal two-local,
and applies generation one to the odd-prime, invariant binary-linear and
Held rows. The prime-five model is transported to PSL₂(4); the binary
rank-one alternative is retained for the subsequent embedding argument.

No closure-classification or model-generation premise remains. The exact
`ModelGenerationAt` contract retains the original ambient hypotheses and
actual quotient models.

Source: Aschbacher--Smith 10.3.3 and its final reuse, pp.756--757,
using E.1.11--14 and the paired E.2.2 calculation.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
variable {G : Type*} [Group G] [Finite G]

/-- Every nonbinary closure model has generation one on its original
component-orbit Sylow join, with all model calculations discharged. -/
theorem modelGeneration (T : Sylow 2 G) : ModelGenerationAt T :=
  modelGeneration_of_moved movedOddPrimeGeneration

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
