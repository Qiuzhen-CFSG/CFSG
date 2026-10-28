module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.LocalMoving
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.LocalPreserving

/-!
# The original exchanged-component calculation

Split according to whether the placed quadratic actor normalizes the selected
component. Both proved branches use the same original action, two-core quotient,
and marked Borel. Their conclusions give the residual commutator inclusion
needed by the original generation-one seed contradiction.

Source: Aschbacher–Smith 15.3.65, printed p.1152.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
variable {G : Type*} [Group G] [Finite G]

/-- The original exchanged-component Borel calculation, with both actor cases discharged. -/
theorem local_commutator_borel_fixed {T : Sylow 2 G} {H M Y ZS Z : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (K : Subgroup H) (f : ℕ) (hmodel : OriginalBorel.OddModel T H M K f)
    (hn : ¬K.Normal) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (hA : IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hq : IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))))
    (hd : fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H)))) :
    subspaceCommutator a.representation ⊤ (actorImage H (residual H)) ⊓
      fixedSpace a.representation (borelImage H M) ≤
      fixedSpace a.representation (actorImage H (residual H)) := by
  by_cases hp : B.map (QuotientGroup.mk' (pCore 2 H)) ≤
      normalizer (actorImage H (K.map H.subtype) : Set (H ⧸ pCore 2 H))
  · exact local_preserving_commutator_borel_fixed hH hP hSQTK a K f hmodel hn B hB hA hq hd hp
  · exact local_moving_commutator_borel_fixed hH hP hSQTK a K f hmodel hn B hB hA hq hd hp

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Exchanged
