module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlockResidual
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryChiefControl
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification

/-!
# The two remaining ordinary source arguments

These are proof targets for the independent module sieve and Baumann argument,
not assumed theorems of 13.3.14. Both retain every literal selected-component
premise of `OrdinaryBlockSource`. The module target identifies the actual W_K
with the A₅ action and proves reduction (g). The chief target may use those
outputs explicitly, and proves the original actor's chief budget.

`Assembly` combines their proofs with intrinsic layer recognition. The source
assembly is incomplete until both targets have been proved under the original
contrary plane-centralization hypothesis.

Source: Aschbacher--Smith, 13.3.14(g) and final paragraph, printed p.893.
-/

@[expose] public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- Target of the module-row sieve, including the original reduction (g). -/
def OrdinaryMovedModuleSource : Prop :=
  ∀ K : Subgroup H, K.IsCComponent →
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) →
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ →
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) →
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K → IsQuasisimple (K ⧸ pCore 2 K) →
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ →
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T →
      (¬ sourceOne L T P ≤ K.map H.subtype) ∧
        Chapter6.Source.IsConjugationModel (K.map H.subtype)
          (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
          Chapter6.Source.a5Module

/-- Target of Baumann escape and the 13.3.10 chief-factor consequence.
It can be proved independently with the preceding module output explicit. -/
def OrdinaryChiefBudgetSource : Prop :=
  ∀ K : Subgroup H, K.IsCComponent →
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) →
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ →
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) →
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K → IsQuasisimple (K ⧸ pCore 2 K) →
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ →
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T →
      (¬ sourceOne L T P ≤ K.map H.subtype) →
      Chapter6.Source.IsConjugationModel (K.map H.subtype)
        (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
        Chapter6.Source.a5Module →
      ∀ s : ChiefSeries (sourceOne L T P),
        s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
