module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Refinement.Rank
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual refined quotient alternatives in 13.1.9

The earlier 13.1.2(3) list is retained as an explicit source premise,
with actual quotient isomorphisms. Three-rank at most one excludes A₆,
its quasisimple triple cover, and G₂(2)′. In the odd branch it makes
the exponent-three quotient cyclic of order three. The other odd primes
are greater than three and retain the original exponent and class bounds.

The earlier five-model classification is discharged by qt-d-1317-source
from its Chapter12 producers. This module proves the refinement, not that
earlier classification.
Source: Aschbacher--Smith 13.1.2(3), p.866, and 13.1.9, p.870.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The literal earlier five-model list. The triple cover retains its
center order and the actual alternating-six central quotient. -/
def FiveQuotients (Q : Type*) [Group Q] : Prop :=
  Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
  ClassicalGroup.IsPSL Q 3 2 ∨
  Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
  (IsQuasisimple Q ∧ Nat.card (center Q) = 3 ∧
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6))) ∨
  Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Exactly the quotient-classification clause of earlier 13.1.2. -/
def QuasisimpleClassification (T : Sylow 2 G) : Prop :=
  ∀ K : Subgroup G, FaithfulMaximalLocal T K → IsQuasisimple (XiQuotient K) →
    FiveQuotients (XiQuotient K)

private theorem threeRank_quotient_le_one {Q : Type*} [Group Q] [Finite Q]
    (hr : primeRank 3 Q ≤ 1) (N : Subgroup Q) [N.Normal] :
    primeRank 3 (Q ⧸ N) ≤ 1 := by
  let P : Sylow 3 Q := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) N

/-- The three-rank bound removes precisely the three larger source models. -/
theorem FiveQuotients.refine {Q : Type*} [Group Q] [Finite Q]
    (hq : FiveQuotients Q) (hr : primeRank 3 Q ≤ 1) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL Q 3 2 := by
  rcases hq with h5 | h3 | h6 | hc6 | hg
  · exact Or.inl h5
  · exact Or.inr h3
  · obtain ⟨e6⟩ := h6
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
    rw [← primeRank_congr 3 e6] at hl
    omega
  · obtain ⟨_,_,⟨e6⟩⟩ := hc6
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
    rw [← primeRank_congr 3 e6] at hl
    have hu := threeRank_quotient_le_one hr (center Q)
    omega
  · obtain ⟨eg⟩ := hg
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := ZMod 2)
    rw [← primeRank_congr 3 eg] at hl
    omega

/-- The d=3 alternative is the concrete cyclic group of order three. -/
theorem OddShape.refine {Y : Subgroup G} (hy : OddShape Y) (hr : primeRank 3 Y ≤ 1) :
    Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3)) ∨
      ∃ d : ℕ, d.Prime ∧ 3 < d ∧ IsPGroup d (XiQuotient Y) ∧
        Monoid.exponent (XiQuotient Y) = d ∧ Group.nilpotencyClass (XiQuotient Y) ≤ 2 := by
  obtain ⟨_,d,hd,ho,hp,he,hc⟩ := hy
  by_cases hd3 : d = 3
  · rw [hd3] at hp he
    have hrQ : primeRank 3 (XiQuotient Y) ≤ 1 := by
      rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup]
    let : IsCyclic (XiQuotient Y) := hp.isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => by
        let := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrQ E)
    have hcard : Nat.card (XiQuotient Y) = 3 := IsCyclic.exponent_eq_card.symm.trans he
    have e := (zmodCyclicMulEquiv (inferInstance : IsCyclic (XiQuotient Y))).symm
    rw [hcard] at e
    exact Or.inl ⟨e⟩
  · have hd2 : d ≠ 2 := by rintro rfl; norm_num at ho
    exact Or.inr ⟨d,hd,by have hh := hd.two_le; omega,hp,he,hc⟩

/-- The refined possibilities retain the original component membership
and two-perfectness, alongside the literal quotient identifications. -/
def RefinedShape (T : Sylow 2 G) (H Y : Subgroup G) : Prop :=
  (Y ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient Y) ∧ FaithfulMaximalLocal T Y ∧
    (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2)) ∨
  (IsPPerfect 2 Y ∧ Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3))) ∨
  (IsPPerfect 2 Y ∧ ∃ d : ℕ, d.Prime ∧ 3 < d ∧ IsPGroup d (XiQuotient Y) ∧
    Monoid.exponent (XiQuotient Y) = d ∧ Group.nilpotencyClass (XiQuotient Y) ≤ 2)

theorem Witness.refined {L H Y : Subgroup G} (w : Witness T L H Y)
    (hclass : QuasisimpleClassification T) (hr : primeRank 3 Y ≤ 1) :
    RefinedShape T H Y := by
  rcases w.alternatives with ho | ⟨hY,hq,hf⟩
  · rcases ho.refine hr with he | he
    · exact Or.inr (Or.inl ⟨ho.1,he⟩)
    · exact Or.inr (Or.inr ⟨ho.1,he⟩)
  · exact Or.inl ⟨hY,hq,hf,(hclass Y hf hq).refine
      (by rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup])⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
