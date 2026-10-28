module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.ProductCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
public import Theory.SpecificGroups.FFG2DerivedCenter

/-!
# Source FF alternatives and their three-prime-core reductions

`Basic` supplies compatible group and representation isomorphisms, concrete
natural and repeated-natural actions, the exceptional four-dimensional
extension, and exclusion of a trivial actor by an FF witness.
`NonQuasisimple` records every clause of B.5.6(2)–(5), while
`QuasisimpleModels` records the full group list in B.5.6(1).

`ProductCore` proves the three-prime-core conclusion for every case in
B.5.6(2)–(5), including the nonsplit hyperplane case. `QuasisimpleCore`
reduces B.5.6(1) to the concrete three-group-center calculation for G₂(2)',
reusing the source's quasisimplicity. All other listed model cores are
proved through their actual matrix, permutation or octonion carriers.

The exhaustive conditional theorem below consumes the full six-clause B.5.1
and B.5.6 inputs and the actual binary derived-center calculation. Neither an
arbitrary class K nor a model label is treated as a classification theorem. No
universal B.5.1 or B.5.6 implication is proved by these exports.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.5.1, printed pp.99–103; B.5.3 and B.5.6, printed
pp.104–110; application in 15.4.18, printed p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The complete conditional FF classification eliminates the actor's
three-prime core. The FF witness removes the degenerate trivial-actor branch;
the remaining quasisimple and nonquasisimple alternatives are discharged by
their actual model and factor core calculations. -/
theorem CompleteClassificationInput.threePrimeCore_eq_bot
    [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    pPrimeCore 3 D = ⊥ := by
  rcases h.groupCases_of_ff ρ hyp hff with ⟨hq, hm⟩ | hnq
  · exact threePrimeCore_eq_bot_of_quasisimple_alternative hm
      (fun _ => Theory.SpecificGroups.g2_derived_two_center_isThreeGroup)
  · exact hnq.threePrimeCore_eq_bot ρ hyp.generated hyp.twoCore

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
