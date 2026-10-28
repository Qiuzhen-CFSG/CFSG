module
public import Stellmacher.SectionFiveToSeven.CriticalPairNormalization

/-!
# Endpoint bounds for critical-pair commutators

The commutator of the centers of any critical pair lies in both centers.
Normalize the pair to an anchored critical path. Result (7.4) puts each
center in the other endpoint stabilizer, which normalizes that endpoint's
center. The two commutator bounds follow, and injective conjugation returns
the original pair. This is the endpoint containment used for both shifted
commutators in Stellmacher (8.2), printed pp.37–38.
Source: `refs/latex/stellmacher-n-group.tex`, (7.4) and (8.2).
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u

public theorem critical_pair_commutator_le_inf
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) (base : CriticalPath Γ)
    (left right : Γ.Vertex) (hcritical : IsCriticalPair Γ left right) :
    ⁅z Γ left, z Γ right⁆ ≤ z Γ left ⊓ z Γ right := by
  obtain ⟨actor, cp, hleft, hright, _⟩ :=
    exists_criticalPath_of_critical_pair h Γ base left right hcritical
  have h74 := lemma_seven_four h Γ cp
  have hleftNorm : z Γ cp.a ≤ Subgroup.normalizer (z Γ cp.a' : Set G) :=
    (h74.first_containment.1.trans h74.first_containment.2).trans
      (stabilizer_le_normalizer_z_public Γ cp.a')
  have hrightNorm : z Γ cp.a' ≤ Subgroup.normalizer (z Γ cp.a : Set G) :=
    h74.reverse_containment.1.trans (stabilizer_le_normalizer_z_public Γ cp.a)
  have hbound : ⁅z Γ cp.a, z Γ cp.a'⁆ ≤ z Γ cp.a ⊓ z Γ cp.a' := by
    apply le_inf
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hrightNorm
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hleftNorm
  rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator,
    ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective] at hbound
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hbound

end Stellmacher.SectionsFiveToSeven
