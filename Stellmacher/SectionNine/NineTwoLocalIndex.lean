module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6

/-!
# The full fixed index in the local action of (9.2)

At the normalized initial edge, the neighboring core intersection lies in
its distinguished Sylow subgroup. If the initial center meets the other
center with index two and the core intersection does not lie in the initial
core, its action has full fixed index two and is nontrivial.

The other center centralizes its core, so its intersection with the initial
center lies in the fixed space. Thus the fixed index divides two. The edge
centralizer equality (7.4) and the core noncontainment exclude index one.
This common reduction precedes both the barred-critical fixedness argument
and the order-four classification in (9.2), printed p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_two_fixed_index
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex) (hm : m ∈ Neighborhood Γ cp.firstStep)
    (hindex : QuotientCardEq (ZAt Γ cp.a) (ZAt Γ cp.a ⊓ ZAt Γ m) 2)
    (hnot : ¬ QAt Γ cp.firstStep ⊓ QAt Γ m ≤ QAt Γ cp.a) :
    let actor := QAt Γ cp.firstStep ⊓ QAt Γ m
    actor ≤ T ∧
      ¬ actor ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) ∧
      ⁅ZAt Γ cp.a, actor⁆ ≠ ⊥ ∧
      QuotientCardEq (ZAt Γ cp.a)
        (ZAt Γ cp.a ⊓ Subgroup.centralizer (actor : Set G)) 2 := by
  let actor := QAt Γ cp.firstStep ⊓ QAt Γ m
  let moduleCenter := ZAt Γ cp.a
  let intersection := moduleCenter ⊓ ZAt Γ m
  let fixed := moduleCenter ⊓ Subgroup.centralizer (actor : Set G)
  have hactorT : actor ≤ T :=
    inf_le_left.trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hnontrivial : ¬ actor ≤ Subgroup.centralizer (moduleCenter : Set G) := by
    intro hcentral
    apply hnot
    have hle := le_inf hactorT hcentral
    exact hle.trans_eq (lemma_seven_four h Γ cp).edge_centralizer
  have hcomm : ⁅moduleCenter, actor⁆ ≠ ⊥ := by
    intro hbot
    apply hnontrivial
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  have hneighbor : cp.firstStep ∈ neighborhood Γ m :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcenter : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three h Γ).center_core m cp.firstStep hneighbor).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))
  have hcontained : intersection ≤ fixed :=
    inf_le_inf_left _ (hcenter.trans (Subgroup.centralizer_le inf_le_right))
  have hintersectionIndex : intersection.relIndex moduleCenter = 2 := by
    have hcard := (intersection.subgroupOf moduleCenter).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show intersection ≤ moduleCenter from inf_le_left)).toEquiv] at hcard
    change intersection.relIndex moduleCenter * Nat.card intersection =
      Nat.card moduleCenter at hcard
    change Nat.card moduleCenter = 2 * Nat.card intersection at hindex
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcard.trans hindex)
  have hdiv : fixed.relIndex moduleCenter ∣ 2 := by
    rw [← hintersectionIndex]
    exact Subgroup.relIndex_dvd_of_le_left moduleCenter hcontained
  have hfixedIndex : fixed.relIndex moduleCenter = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · have hle := Subgroup.relIndex_eq_one.mp hone
      exact (hnontrivial (Subgroup.le_centralizer_iff.mp
        (hle.trans inf_le_right))).elim
    · exact htwo
  refine ⟨hactorT, hnontrivial, hcomm, ?_⟩
  have hcard := (fixed.subgroupOf moduleCenter).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show fixed ≤ moduleCenter from inf_le_left)).toEquiv] at hcard
  change fixed.relIndex moduleCenter * Nat.card fixed = Nat.card moduleCenter at hcard
  rw [hfixedIndex] at hcard
  exact hcard.symm


end Stellmacher.SectionNine
