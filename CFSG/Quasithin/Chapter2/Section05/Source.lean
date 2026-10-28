module
public import CFSG.Quasithin.Chapter2.Section05.SourceCases
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.Source
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.LinearThreeSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.StarredSourceSetup

/-!
# The original empty characteristic-two family is impossible

The starred source tuple is constructed from the actual unique maximal
local subgroup and nonempty delta. The complete source component catalogue
then splits into A₆, prime PSL₂ (including PSL₃(2)), PSL₃(3), and M₁₁.
Their original source contradictions eliminate every branch. Consequently
the characteristic-two Gamma-zero family is nonempty, as required to pass
from the original Theorem 2.1.1 hypotheses into §2.4.

Source: Aschbacher--Smith, completion of Theorem 2.1.1, printed p.570.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Every alternative of the original starred source tuple is impossible. -/
theorem original_source_setup_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M) : False := by
  apply ComponentSelection.MathieuSourceSetup.source_false_of_prime_and_ternary
    c hG hempty hgen hb hstar
  · intro p _ hp hfm eK
    exact ComponentSelection.MathieuSourceSetup.prime_source_false
      c hG hempty hgen hb hstar hp hfm eK
  · intro eK
    exact CFSG.Quasithin.Chapter2.Section05.MathieuSourceSetup.linear_three_three_source_false
      c hG hempty hgen hb hstar eK

/-- The original nonempty-delta hypotheses force a characteristic-two
Gamma-zero overgroup; no selected component or shadow premise is assumed. -/
theorem gammaEvenZero_nonempty_of_delta_nonempty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) :
    (gammaEvenZero (Chapter1.He G) M).Nonempty := by
  by_contra he
  have hempty := Set.not_nonempty_iff_eq_empty.mp he
  obtain ⟨H,K,S,z,c,hstar,hb,hgen⟩ := exists_starred_source_setup
    hG T hM hTM hunique hdelta hempty
  exact original_source_setup_false c hG hempty hgen hb hstar

end CFSG.Quasithin.Chapter2.Section05
