module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Core
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Residual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Natural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Assembly

/-!
# Assembly of the original diagonal-centralizer seed calculations

The local odd-residual calculation supplies the seed-join core bound and
the prime-to-three residual identity. The latter yields the required relative
normality. The disjoint-factor argument fixes the two original vectors.
The independent natural-module calculation supplies the commutator supplement.

The two earlier calculation inputs remain explicit here. Their producers
must discharge them before this is an unconditional SeedAnalysisAt theorem.
The final CoreReducedAt assembly retains its separate full-action input.

Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- All five fields on the same original configuration, from the two remaining calculations. -/
theorem analysis_of_calculations (c : Configuration s a b) (h : LocalCalculation c)
    (hgen : D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔
      (zpowers a ⊔ zpowers b)) : SeedAnalysis c where
  core_bound := core_bound h
  commutator := h.commutator
  normal_in_kernel := normal_in_kernel_of_twoThree s h.prime_spectrum
  fixes := fixes c
  generates := hgen

/-- Conditional assembly; the local and natural-action obligations are not discharged here. -/
theorem seedAnalysisAt_of_calculations
    (hlocal : LocalCalculationAt T) (hmodule : ModuleGenerationAt T) : SeedAnalysisAt T := by
  intro L D s a b c
  exact analysis_of_calculations c (hlocal L D s a b c) (hmodule L D s a b c)

/-- Application to the original centralizer two-core and full-action reducedness contract.
The independent full-action representation argument is retained with its assembly owner. -/
theorem coreReduced_of_calculations
    (hlocal : LocalCalculationAt T) (hmodule : ModuleGenerationAt T)
    (haction : FullActionCentralizationAt T) : CoreReducedAt T :=
  coreReduced_of_source_inputs (seedAnalysisAt_of_calculations hlocal hmodule) haction

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
