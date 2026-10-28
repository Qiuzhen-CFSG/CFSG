module
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.NormalTerminal
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Normality

/-!
# The original prime component branch

The original bad-involution argument proves component normality in H.
The exact quotient and core exclusions select its nonabelian dihedral core
and marked crossing. The preceding component persistence theorem then gives
normality in every core-involution centralizer. The proved prime reduction
supplies fixed generation and the complete crossing-pair contradiction.

Source: Aschbacher--Smith 2.5.19--21, printed pp.560--567.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Overcomponents
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original prime component contradiction with every earlier source
hypothesis discharged on the literal tuple. -/
theorem MathieuSourceSetup.prime_source_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p)) : False := by
  let : (K.subgroupOf H).Normal := source_component_normal c hG hempty hgen hb hstar
  exact MathieuSourceSetup.prime_source_false_of_normal_component
    c hG hempty hgen hb hstar hp hfm eK

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
