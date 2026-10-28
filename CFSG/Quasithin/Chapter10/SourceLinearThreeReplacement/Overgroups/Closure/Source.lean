module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Complete.Source

/-!
# The normal-closure alternatives for the original centralizer seed

The original paired natural action realizes the diagonal centralizer as a
maximal parabolic of L₀T. Its embedded two-residual is exactly
X = O²(C_{L₀}(z)), and its two-core quotient is S₃ wr C₂. The intrinsic
embedding theorem then identifies the normal closure of X in each containing
maximal two-local with X or an actual component orbit. The wreath action
sieves the invariant classical rows and supplies the full Aut(L₄(2)) or
Aut(L₅(2)) quotient. The adequate intrinsic Held alternative is retained.

Both earlier-source inputs to the conditional closure assembly are now
discharged. The overgroup-span application retains only the independent
model-generation input, whose final discharge belongs to its assembly owner.

Source: Aschbacher--Smith 10.2.4, printed p.747, applied to the centralizer
seed of 10.2.11 in the final argument of §10.3, pp.756--757.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
variable {G : Type*} [Group G] [Finite G]

/-- The exact published closure contract, with parabolic recognition and
the invariant wreath-action sieve proved from their original hypotheses. -/
theorem closureAlternatives (T : Sylow 2 G) : ClosureAlternativesAt T :=
  closureAlternatives_of_seed_and_sieve (Parabolic.parabolicSeed T)
    (invariantWreathSieve T)

/-- Discharge the closure-classification input for the original overgroup
span; the separate model-generation argument remains explicit. -/
theorem overgroupSpan_of_generation {T : Sylow 2 G}
    (hgeneration : ModelGenerationAt T) : OvergroupSpanAt T :=
  overgroupSpan_of_source_inputs (closureAlternatives T) hgeneration

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
