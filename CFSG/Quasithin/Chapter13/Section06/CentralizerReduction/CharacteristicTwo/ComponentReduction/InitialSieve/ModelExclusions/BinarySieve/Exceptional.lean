module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.ActionTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinaryIdentification
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.G2
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.Ree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.Triality
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.MixedFixers

/-!
# Exceptional binary component branches

The G₂, genuine triality and Ree field branches, and the exclusion of actual
G₂(2)′, are complete. The proved inner–field and inner–coefficient coverage
theorems discharge the intrinsic premises of the G₂ and triality reductions.
The mixed triality fixer theorem handles even exponents; odd exponents use
the odd coefficient quotient. At exponent one, the actual Sylow center has
order two and cannot contain the faithful marked four-group.

All branches use the faithful action on the component's central quotient,
retaining G₂(4) central covers and the Ree field exponent 2*n+1. Simplicity
and perfectness in the triality application are inherited from that quotient.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, conditional on
the genuine 1.1.5(3)(a,b), printed pp.501–503. The conclusions below use only
the actual component, its marked action data and the specified model; no
intrinsic automorphism premise remains.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module ClassificationModels
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The G₂ field branch, including the nontrivial central cover at field order four. -/
theorem largeField_of_g2
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 2 ≤ m)
    (hi : IsG2At (NormalizerAction.componentImage K) (2 ^ m)) :
    LargeField K a :=
  largeField_of_g2_of_coverage
    (fun _ _ _ _ hq => Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hq)
    K hK a hm hi

/-- The genuine triality model at exponent one cannot support the source central four-group. -/
theorem triality_exponent_gt_one
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 ≤ m)
    (hi : Triality.Standard.IsTrialityGroupAt (2 ^ m) (NormalizerAction.componentImage K)) :
    1 < m :=
  triality_exponent_gt_one_of_coverage
    (fun n hn hs hp => @Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient
      n hn hs hp)
    K hK a hm hi

/-- The complete triality branch: the defining exponent is greater than one and
the literal marked four-group lies in the component image. -/
theorem largeField_of_triality
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 ≤ m)
    (hi : Triality.Standard.IsTrialityGroupAt (2 ^ m) (NormalizerAction.componentImage K)) :
    LargeField K a :=
  largeField_of_triality_of_coverage_and_mixed_fixers
    (fun n hn hs hp => @Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient
      n hn hs hp)
    (fun n hn _ _ heven α k hpow hform hfix =>
      Triality.Standard.EvenInvolutionGeometry.inner_of_even_exponent n hn heven α
        (k := k) hpow hform hfix)
    K hK a hm hi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
