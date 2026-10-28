module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Source

/-!
# Replacement consumers with moved-prime generation discharged

The complete moved-prime theorem closes the last model-generation row.
It also discharges the shared input to the non-Bender wreath argument.
The independent normal-closure and earlier seed premises stay with the
source assembly owners qt-d-10-replacement-overgroup-span and
qt-d-10-replacement-wreath-recognition; this module introduces none of
those premises into the unconditional moved-prime theorem.

Source: Aschbacher--Smith 10.3.3 and its final reuse, pp.756--757.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

namespace Overgroups.ModelGeneration

/-- All model rows in the original overgroup-span consumer are discharged. -/
theorem modelGeneration : ModelGenerationAt T :=
  modelGeneration_of_moved movedOddPrimeGeneration

/-- Only the independently owned closure classification remains in the span assembly. -/
theorem overgroupSpan_of_closure (hclosure : ClosureAlternativesAt T) : OvergroupSpanAt T :=
  overgroupSpan_of_moved hclosure movedOddPrimeGeneration

end Overgroups.ModelGeneration

namespace NonBender

/-- Application to the exact non-Bender contract with the moved-prime input discharged. -/
theorem nonBenderGeneration_of_normal_and_parabolic_seed
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T) : NonBenderGenerationAt T :=
  nonBenderGeneration_of_remaining hnormal hseed Overgroups.ModelGeneration.movedOddPrimeGeneration

/-- The final wreath owner retains the independent Bender and earlier-source seed proofs. -/
theorem wreathRecognition_of_bender_and_seeds (hB : BenderRecognitionAt T)
    (hnormal : NormalSeedBenderAt T)
    (hseed : Overgroups.Closure.ParabolicSeedAt T) : WreathRecognitionAt T :=
  wreathRecognition_of_remaining hB hnormal hseed Overgroups.ModelGeneration.movedOddPrimeGeneration

end NonBender
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
