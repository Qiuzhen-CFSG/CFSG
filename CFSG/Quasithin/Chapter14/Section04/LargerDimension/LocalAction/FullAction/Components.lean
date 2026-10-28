module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Projection

/-!
# The selected component in 14.4.8(2)

Selection constructs an actual maximal faithful local component covering the
moved-space action, with its PSL₃(2) two-core quotient. Projection constructs
the marked map to that quotient and places both cubic generators in the
component. Their join is therefore the component itself. The theorem below
combines these two arguments for the literal source Y-family.

The full LXT action is the conclusion of
`full_conjugation_of_earlier_extraspecial_data`. The outer assembly supplies
its earlier 12.8 premises from genuine Hypothesis 14.3.10 in the extraspecial
d > 4 branch, along with the earlier residual, cubic-quotient and normalization
facts for L₂. The universal inputs here are precisely 1.2.1(1) and
14.3.4(1--2); their discharge remains with that assembly. Neither a component
placement nor an action-kernel identification is assumed. The natural-module
clause 14.3.4(3) is not needed for this component argument.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, p.1009.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section04

variable {G : Type*} [Group G] [Finite G]

/-- The component conclusion of 14.4.8(2), from the earlier universal
implications and the full literal moved-space action. Selection proves
applicability of 14.3.4 and excludes A₅; the marked projection then proves
that both generators lie in the selected component, identifying it with LX.
The source action and parabolic conclusions remain with `FullAction`. -/
theorem localJoin_mem_LStar_of_full_join_action
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H V₂ E X L₂ : Subgroup G} (hX : X ∈ YFamily H T V₂ E)
    [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hV₂T : V₂ ≤ T) (hL₂ : twoResidual L₂ = L₂)
    (hLc : Nat.card (coreQuotient L₂) = 3)
    (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G))
    (hn : localJoin L₂ X ⊔ (T : Subgroup G) ≤ normalizer (movedSpace V₂ X : Set G))
    (hs : Function.Surjective
      (conjugation (localJoin L₂ X ⊔ (T : Subgroup G)) (movedSpace V₂ X) hn)) :
    localJoin L₂ X ∈ Chapter1.LStar G T ∧
      IsFaithfulSignalizerType (localJoin L₂ X) ∧
      Nonempty (coreQuotient (localJoin L₂ X) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨S⟩ := exists_selectedComponent_of_full_join_action earlier T hE
    classification hX hV₂T hL₂ hTL₂ hn hs
  obtain ⟨_, _, _, _, heq⟩ := selectedComponent_eq_localJoin T hX hL₂ hLc hTL₂ hn S
  rw [heq]
  exact ⟨S.maximal, S.faithful, S.quotient⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
