module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Adequate
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Held
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers

/-!
# The retained Held alternative on the original intrinsic input

The proved odd-primary covering theorem and trivial two-core identify the
whole quasisimple group with the actual Held carrier. Its existing Sylow-pair
coverage gives an elementary plane. Transport through the literal component
quotient supplies precisely the HeldAlternative consumed by the adequate
intrinsic theorem; no automorphism realization or blanket Held exclusion is
needed for this conclusion.

Source: Aschbacher–Smith, the intrinsic reduction at printed pp.510–511;
the retained Held case is documented in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
universe u

/-- The actual Held central quotient supplies both the plane and the whole-group model. -/
theorem surviving_of_source
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ⧸ center Q ≃* Held.He) :
    Nonempty (R ≃* Plane 3) ∧ Nonempty (Q ≃* Held.He) := by
  let : IsQuasisimple Q := h.quasisimple
  have hz := Held.OddPrimary.source_center_isPGroup ⟨e⟩
  let j := SporadicActions.centralQuotientEquiv h.twoCore hz e
  have hi := pairInput_of_equiv h j
  have he := plane hi
  exact ⟨he.map (fun f => (j.subgroupMap R).trans f), ⟨j⟩⟩

/-- Original local and Sylow hypotheses give the exact retained Held alternative. -/
theorem held_of_local_input {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hm : Nonempty (XiQuotient L ⧸ center (XiQuotient L) ≃* Held.He)) :
    HeldAlternative 3 T P L := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, _, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  obtain ⟨he, hmodel⟩ := surviving_of_source hi hm.some
  exact ⟨rfl, plane_of_quotient_plane h hPL he, hTL, hmodel⟩
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
