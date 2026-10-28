module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainedSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimpleQuotient
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
/-!
# The original normalized A₅ source: index two or an escaping component

The A₅ block supplies its genuine quasisimple core quotient. In the
contained-preimage branch the original L is an ambient C-component and
M has index two. Otherwise C.2.11 selects an actual escaping C-component,
normalized by this same L, with ordinary or characteristic-two structure.
No classification row, marking or component witness is assumed.

This is the C.2.11–13 prefix of the specialized C.4.8/4.3.2 source.
The larger-component models remain the C.3/C.4 classification obligation.
Source: Aschbacher–Smith C.2.11–13 and C.4.8, pp.148,153;4.3.2,p.613.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}
/-- The literal A₅ source consumer, with its core quotient discharged internally. -/
theorem alternating_five_component_alternative
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hnorm : M ≤ normalizer (L : Set G)) (hstrict : M < H)
    (hblock : IsAlternatingBlock L 5) (hU : (blockU L).map L.subtype = V) :
    ((generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H ∧
      (L.subgroupOf H).IsCComponent ∧ (M.subgroupOf H).index = 2) ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ L ≤ normalizer (K.map H.subtype : Set G) ∧
      (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  have hs : conjugateSpanBy L M = L :=
    le_antisymm (conjugateSpanBy_le le_rfl hnorm) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect L := hs ▸ h.span_perfect
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (show IsChiZeroBlock L from .inr (.inr hblock)).simple_quotient
  have hz : center (L ⧸ pCore 2 L) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh))
  let : IsQuasisimple (L ⧸ pCore 2 L) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  rcases h.component_source_alternative with hf | ⟨K,hK,hq,hout,hn,hcase⟩
  · exact .inl ⟨hf,h.index_two_of_fitting_contained hnorm hstrict hU hf⟩
  · exact .inr ⟨K,hK,hq,hout,by simpa only [hs] using hn,hcase⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
