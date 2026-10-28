module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.SourceAssembly
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2.OuterDescent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality.Source
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders

/-!
# E.6.18 after the concrete Lie and Mathieu model calculations

The actual G₂ outer descent, all triality involution data and the M₂₄
fixed-point-free centralizer order bound instantiate the remaining Lie and
Mathieu fields of the full catalogue dispatch. All earlier source inputs
are already discharged in SourceAssembly. The original ambient conclusion
retains exactly the Rudvalis second-row order bound and the Held cover-center
theorem. These two genuine model obligations are not asserted here.

Source: Aschbacher–Smith E.6.18, printed p.252.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
universe u

/-- The complete catalogue input, apart from the one remaining Rudvalis row. -/
theorem sevenInspectionModelFacts_of_rudvalis_order
    (hRu : ¬ 9 ∣ Nat.card (Rudvalis.InvolutionCentralizers.Centralizer Rudvalis.a)) :
    SevenInspectionModelFacts := by
  refine ⟨BinaryLie.G2.outerInvolutionDescent, BinaryLie.triality_models_source,
    (fun n hn _ _ => BinaryLie.triality_inner_source n hn), ?_,
    Sporadic.Mathieu.M24InvolutionFixedOrders.centralizer_twoB_not_nine, hRu⟩
  intro n hn _ _ a ha hi
  obtain ⟨m,hm,hnm,he⟩ := BinaryLie.triality_outer_source n hn a ha hi
  exact ⟨m,hm,by omega,he⟩

/-- The exact original E.6.18 output with only the two outstanding sporadic
model facts explicit. Original actions, component embeddings and centralizer
maps are retained throughout the source assembly. -/
theorem sevenExcluded_of_rudvalis_order_and_held_center
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M V : Subgroup G}
    (hRu : ¬ 9 ∣ Nat.card (Rudvalis.InvolutionCentralizers.Centralizer Rudvalis.a))
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) :
    Enlargement.SevenExcluded M V :=
  sevenExcluded_of_remaining_model_facts
    (sevenInspectionModelFacts_of_rudvalis_order hRu) hHeld h h15

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
