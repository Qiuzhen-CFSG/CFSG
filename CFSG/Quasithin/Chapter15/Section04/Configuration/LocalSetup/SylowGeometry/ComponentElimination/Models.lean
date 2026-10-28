module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.FermatMersenne

/-!
# The ordinary-component reduction output

These definitions specify the intermediate output needed from the two
C-component alternatives in the first paragraph of printed p.1164. They
retain ordinary relative component inclusions, the actual factor product,
its conjugation permutation, concrete models and inner-action witnesses.
They are output contracts, not an assertion that a C-component is ordinary
or that the source model reduction has been proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; 1.1.5(3), printed pp.501–503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
variable {G : Type*} [Group G]

/-- The two actual ordinary components, with their product and permutation. -/
structure OrdinaryComponentPair (H K U : Subgroup G) where
  factor : Bool → Subgroup G
  le_overgroup : ∀ i, factor i ≤ H
  component : ∀ i, IsComponent H ((factor i).subgroupOf H)
  product : factor false ⊔ factor true = K
  action : TwoFactors.MixedLocal.FactorPairAction U factor

/-- Every actor is implemented by an element of the same actual component. -/
def CentralInnerAction (L Z : Subgroup G) : Prop :=
  ∀ z : Z, ∃ l : L, ∀ x : L,
    (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹

/-- Ordinary models and actions after the genuine 1.1.5 comparison.
Constructing this proposition from the source C-component alternatives is
required before any of the conditional obstructions can finish the branch. -/
def OrdinaryAlternatives (H K U Z : Subgroup G) : Prop :=
  (IsComponent H (K.subgroupOf H) ∧
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL K n 2) ∧
    CentralInnerAction K Z) ∨
  ∃ d : OrdinaryComponentPair H K U,
    ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ 5 ≤ p ∧
      ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 p) ∨
     (∃ n : ℕ, Even n ∧ 2 ≤ n ∧
      ∀ i, ClassicalGroup.IsPSL (d.factor i) 2 (2 ^ n))) ∧
    ∀ i, CentralInnerAction (d.factor i) Z

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
