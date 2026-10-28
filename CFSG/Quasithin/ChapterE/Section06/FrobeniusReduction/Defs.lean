module

public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.Representation.RegularCyclicNormalClosure.Defs

/-!
# The earlier structural input to E.6.24

`RegularCyclicSection` records the cyclic subgroup supplied by E.6.11(2):
its faithful image, order, regular action, relative normality, and internal
direct decomposition of V. It asserts no conclusion of E.6.24 or E.6.25.
The E.6 owner must construct this input from E.6.11. The reduction also
retains the genuine HypothesisE61, membership in Γ, and corank bounds.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.250 and 255 (PDF pp.261 and 266).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction

open Subgroup

variable {G : Type*} [Group G]

/-- The exact cyclic-action data used from the earlier E.6.11(2). Its
placement inside the component or block L is supplied separately. -/
structure RegularCyclicSection (M V U X : Subgroup G) : Prop where
  contained : X ≤ localNormalizer M V ⊓ centralizer (U : Set G)
  cyclic : IsCyclic X
  card_eq : Nat.card X = 2 ^ subgroupCorank V U - 1
  faithful : X ⊓ centralizer (V : Set G) = ⊥
  fixed : V ⊓ centralizer (X : Set G) = U
  spanning : U ⊔ ⁅V, X⁆ = V
  disjoint : U ⊓ ⁅V, X⁆ = ⊥
  regular : ∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ w ∈ ⁅V, X⁆, w ≠ 1 →
    ∃! x : X, (x : G) * v * (x : G)⁻¹ = w
  normal_image : ((inducedAutomizer V X).subgroupOf
    (inducedAutomizer V (localNormalizer M V ⊓ normalizer (U : Set G)))).Normal

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
