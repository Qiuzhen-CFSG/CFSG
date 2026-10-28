module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.A5ActionRank
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedParabolic

/-!
# The constrained symplectic row in the original A₅ configuration

The genuine C.2.7 symplectic star marking makes the selected component
normal and bounds the actual span action's five-rank by one. Source C.4.3
makes that action nontrivial. The original A₅ pair action retains rank at
least two if M moves L, so M must normalize L.

All action-kernel, normality, intersection and nontriviality premises are
proved by the imported source theorems. The displayed star marking is the
literal row of the C.2.7 catalogue, not an assumed pair representation.

Source: Aschbacher–Smith C.4.5–8, printed pp.152–154; the A₅ covering
consumer is 4.2.12–13, printed pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The actual constrained symplectic model closes the required normality branch. -/
theorem normalizes_of_a5_constrained_symplectic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (eA : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Sp F)
    (hF : 4 ≤ Nat.card F) : M ≤ normalizer (L : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : K.Normal := h.constrained_symplectic_component_normal K hK hq hout hfK e hF
  exact h.normalizes_of_a5_component_action_fiveRank_le_one eA K
    (h.constrained_span_action_nontrivial K hK hq hout)
    (h.constrained_symplectic_span_rank_le_one K hK hq hout hfK e hF (by decide : Odd 5))

end CFSG.Quasithin.ChapterC.HypothesisC28
