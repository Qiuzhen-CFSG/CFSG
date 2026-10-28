module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Source

/-!
# Remaining local source input for the large extraspecial branch

The original 14.4.8 action is required for each member of the literal Y-family,
with I₂, L₂ and V₂ still taken from the caller's flag. The unique maximal
2-local over LT is the earlier source M = N_G(L). The second actor and its
middle quotient are separate outputs of 14.4.9–12. Neither input includes
incidence geometry or recognition of the generated group.

Source: Aschbacher--Smith, 14.3.3, 14.4.8–13, pp.990,1009–1012.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open LargerDimension LargerDimension.LocalAction
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Exact local output consumed by the three-vertex assembly. Its construction
must discharge the earlier extraspecial and component-generation inputs of
`LocalAction.source_lemma_14_4_8`, as well as the actual maximal-overgroup
uniqueness. It contains no conclusion about the second Y-member. -/
structure LocalSourceData (T : Sylow 2 G) (L V : Subgroup G)
    (F : InvariantFlag T V 3) (g : G) where
  action : ∀ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) →
    FullMovedSpaceAction T (F.I₂ L) (F.Li L 2) (F.Vi 2) X
  unique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K →
    K = normalizer (L : Set G)

/-- The output of the surviving marked-model branches, on the same actual
conjugate intersection and the same L₁. This is an output contract only. -/
@[expose] def Partner (T : Sylow 2 G) (L V : Subgroup G) (F : InvariantFlag T V 3) (g : G) : Prop :=
  ∃ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧ X ≠ F.Li L 1 ∧
    Nonempty (coreQuotient (F.Li L 1 ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
