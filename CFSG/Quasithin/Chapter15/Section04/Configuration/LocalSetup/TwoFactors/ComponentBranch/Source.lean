module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Assembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting

/-!
# Elimination of the mixed-factor component branch

Under the raw mixed configuration and the applicable earlier 1.1.5 conclusions,
the generalized Fitting subgroup of I is its two-core. If it were not, trivial
O(I) would supply a component. F.6.11 and the universal F.6.18 implication
classify the literal quotient I/O_{3′}(I). `ModelLifting` controls the central
kernel on the component and extracts an actual original-component model from
every row. `Assembly` constructs its faithful Z-action, selects A₆ and S₆,
and applies the local recognition and incompatible two-rank bounds.

No component catalogue, later model identification, local splitting or
centralizer index is an input. F.6.11 and the residual calculation used from
F.6.6 are proved in the imported development. The universal F.6.18 row
implication remains the authorized classification input; its row (2) permits
all extensions by E₄ of the extraspecial three-group, and the proof excludes
that entire solvable class.

The parent must construct the realized factors, common pre-branch conclusions
and actual 1.1.5 actions, and ultimately instantiate the source class K with
the full known-simple catalogue. This conditional branch theorem does not
complete 15.4.18: the characteristic-two branch and the final factor-count
assembly remain with `TwoFactors`.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163; F.6.6, F.6.11 and F.6.18, pp.305–310; 1.1.5, pp.501–503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
open MixedLocal AlternatingLocals.RawQuotient FFBranch.ClassificationComparison
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The component branch of 15.4.18 is impossible under its raw mixed inputs.
The original-component model premise of the conditional assembly is discharged
by the complete quotient-row and central-kernel lifting argument. -/
theorem generalizedFitting_eq_twoCore_of_source
    {K : GroupClass} (source : F618Universal K)
    (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (hcomm : F false ≤ centralizer (F true : Set G))
    (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hodd : pPrimeCore 2 (generated T Y F) = ⊥)
    (h115 : ∀ L : Subgroup (generated T Y F), IsComponent (generated T Y F) L →
      mixedZ T Y F ≤ normalizer (L : Set (generated T Y F)) ∧
        mixedZ T Y F ⊓ centralizer (L : Set (generated T Y F)) = ⊥)
    (hc : ∀ z : mixedZ T Y F, z ≠ 1 →
      HasCharacteristicTwo (centralizer ({(z : generated T Y F)} : Set (generated T Y F))))
    (hmodels : ∀ L : Subgroup (generated T Y F), IsComponent (generated T Y F) L →
      ∀ z : mixedZ T Y F, z ≠ 1 → HasModelAction115 L (z : G)) :
    generalizedFitting (generated T Y F) = pCore 2 (generated T Y F) := by
  apply generalizedFitting_eq_twoCore_of_component_models T d c hcomm hY hF hZ hodd h115 hc
  intro L hL
  exact ModelLifting.mixed_intrinsicModel source T d c hZ hodd L hL
    (h115 L hL).1 (h115 L hL).2 hc (hmodels L hL)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
