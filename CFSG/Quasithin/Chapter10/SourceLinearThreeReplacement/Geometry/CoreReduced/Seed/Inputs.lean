module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Inputs
public import Theory.GroupTheory.PResidual.ThreeFree

/-!
# Remaining natural-action calculations for the diagonal seed

The local centralizer has only primes two and three, its two-residual is
not a two-group, and every T-normal subgroup outside T₁ generates that
residual by commutators. Separately, the actual natural module is generated
by its X-commutators and the original two fixed vectors. These are independent
source obligations, not established consequences of the record definitions.

Source: Aschbacher--Smith 10.2.11, printed pp.753--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- Calculations on the literal original local centralizer and its two-residual. -/
structure LocalCalculation (_c : Configuration s a b) : Prop where
  prime_spectrum : IsPiGroup twoThreePrimes
    (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G)
  not_two : ¬ IsPGroup 2 (centralizerSeed T L (a*b))
  commutator : ∀ R : Subgroup G, R ≤ (T : Subgroup G) →
    (T : Subgroup G) ≤ normalizer (R : Set G) →
    ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ⁅centralizerSeed T L (a*b), R⁆ = centralizerSeed T L (a*b)

/-- The local odd-residual computation, independent of the representation supplement. -/
def LocalCalculationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (a b : G) (c : Configuration s a b),
      LocalCalculation c

/-- The natural-action supplement on the original full module and original seed. -/
def ModuleGenerationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (a b : G), Configuration s a b →
      D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔ (zpowers a ⊔ zpowers b)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
