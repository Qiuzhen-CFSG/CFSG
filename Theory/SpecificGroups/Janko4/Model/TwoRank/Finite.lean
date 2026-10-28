module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.FixedBound
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Native
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Checked

/-!
# The elementary fixed-mask bound for the actual J₄ max1 action

The existing Sylow enumeration covers each elementary subgroup by the 192
checked candidate vertices. Its order is a power of two. The branching
certificate bounds the product of the size of this commuting set and its
common fixed masks. `Finite.Native` identifies both relations with the literal
permutation subgroup and its direct eleven-coordinate action.

This discharges the finite premise of `TwoRank.Reduction`, used in the J₄ case
of Aschbacher–Smith G.7.3(2), printed pp.347–348 (PDF pp.358–359), citing
Asc82a and GLS98 5.2.10/5.6.1. ATLAS word and coordinate provenance is retained
in `Cardinality.Subgroup`, `Image.StarData`, and `SylowCore.Transport`.
-/
@[expose] public noncomputable section
namespace Janko4.TwoRank
open LocalStructure.SylowCore LocalStructure.SylowCore.FiniteBoundCertificate
open Simplicity.Max1Fusion.QuotientInvolutions
open _root_.Janko4.TwoRank.Finite

private def vertexEquiv (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B] :
    {v : Fin 192 // element (vertex v) ∈ B} ≃ B :=
  Equiv.ofBijective (fun v => ⟨element (vertex v.val), v.property⟩) (by
    constructor
    · intro v w h
      exact Subtype.ext (vertex_injective (element_injective (congrArg Subtype.val h)))
    · intro b
      obtain ⟨v, hv⟩ := native_coverage b.val
        (elemPow_eq_one_of_isElementaryAbelian b.val b.property)
      refine ⟨⟨v, ?_⟩, Subtype.ext hv⟩
      rw [hv]
      exact b.property)

/-- Every elementary subgroup satisfies the fixed-mask inequality; normality is not needed. -/
theorem elementaryFixedBound : ElementaryFixedBound := by
  intro B hB
  classical
  let := hB
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => element (vertex v) ∈ B)
  let z : Finset (Fin 2048) := Finset.univ.filter
    (fun m => ∀ b : B, starMask b.val.val m.val = m.val)
  have hsCard : s.card = Nat.card B := by
    rw [← Nat.card_congr (vertexEquiv B)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, s]
  have hzCard : z.card = Nat.card (FixedMasks B) := by
    simp only [FixedMasks, Nat.card_eq_fintype_card, Fintype.card_subtype, z]
  have hp : ∃ k : ℕ, s.card = 2 ^ k := by
    rw [hsCard]
    exact (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hc := Theory.GroupAction.BinaryCliqueFixedBound.check_sound
    compatible fixed 2048 tree000 (List.finRange 192) (List.finRange 2048)
    tree_checked s z
    (fun v _ => List.mem_finRange v)
    (fun m _ => List.mem_finRange m) hp
    (fun v hv w hw => native_compatible B v w
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2)
    (fun v hv m hm => native_fixed B v (Finset.mem_filter.mp hv).2
      ⟨m, (Finset.mem_filter.mp hm).2⟩)
  simpa only [hsCard, hzCard] using hc

end Janko4.TwoRank
