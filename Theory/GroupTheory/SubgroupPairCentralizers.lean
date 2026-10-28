module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Centralizer control for a pair of subgroups

These lemmas turn element-centralizer containment into normalizer containment,
trivial intersections of conjugates, and a lower bound on subgroup index.
The last argument uses the injection of cosets of `U ∩ W` in `W` into cosets
of `U ∩ V` in `V`: a sufficiently large `W` must meet `U` nontrivially.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript, 1 March 2004, Proposition 10.2.9 and Lemma 10.2.10,
printed pp. 750–753. These elementary implications are independent of the
quasithin hypotheses used there to establish the centralizer containment.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- If `M` permutes two subgroups and contains the centralizer of an element
of the first outside the second, that centralizer normalizes the first.
This is the implication (1) ⇒ (3) in Aschbacher–Smith 10.2.9. -/
public theorem centralizer_le_normalizer_of_conj_pair (M U W : Subgroup G)
    (hperm : ∀ g ∈ M, U.map (MulAut.conj g) = U ∨ U.map (MulAut.conj g) = W)
    {v : G} (hv : v ∈ U) (hvw : v ∉ W)
    (hcent : centralizer ({v} : Set G) ≤ M) :
    centralizer ({v} : Set G) ≤ M ⊓ normalizer (U : Set G) := by
  intro g hg
  refine ⟨hcent hg, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  rcases hperm g (hcent hg) with heq | heq
  · exact heq
  · exfalso
    apply hvw
    rw [← heq]
    refine ⟨v, hv, ?_⟩
    have hcomm := mem_centralizer_singleton_iff.mp hg
    change g * v * g⁻¹ = v
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- Trivial intersections outside a subgroup permuting a disjoint pair imply
that either member of the pair is a TI-subgroup in the ambient group.
This is the implication (1) ⇒ (2) in Aschbacher–Smith 10.2.10. -/
public theorem map_conj_eq_or_inf_eq_bot_of_conj_pair (M U W : Subgroup G)
    (hperm : ∀ g ∈ M, U.map (MulAut.conj g) = U ∨ U.map (MulAut.conj g) = W)
    (hdis : U ⊓ W = ⊥)
    (hout : ∀ g ∉ M, U ⊓ U.map (MulAut.conj g) = ⊥) :
    ∀ g : G, U.map (MulAut.conj g) = U ∨ U ⊓ U.map (MulAut.conj g) = ⊥ := by
  intro g
  by_cases hg : g ∈ M
  · rcases hperm g hg with heq | heq
    · exact Or.inl heq
    · exact Or.inr (heq ▸ hdis)
  · exact Or.inr (hout g hg)

/-- If all nonidentity elements of `W` have centralizer in `M`, then so does
any subgroup whose index in `V ≥ W` is smaller than the order of `W`.
This is the group-theoretic index bound underlying Aschbacher–Smith 10.2.9(2). -/
public theorem centralizer_le_of_relIndex_lt_card (M U W V : Subgroup G) [Finite V] (hWV : W ≤ V)
    (hindex : U.relIndex V < Nat.card W)
    (hcent : ∀ x ∈ W, x ≠ 1 → centralizer ({x} : Set G) ≤ M) :
    centralizer (U : Set G) ≤ M := by
  have hidx0 : U.relIndex V ≠ 0 := by
    change Nat.card (V ⧸ U.subgroupOf V) ≠ 0
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hne : U ⊓ W ≠ ⊥ := by
    intro hbot
    have hidx := relIndex_le_of_le_right hWV hidx0
    rw [← inf_relIndex_right U W, hbot, relIndex_bot_left] at hidx
    exact (not_lt_of_ge hidx) hindex
  have : Nontrivial ↥(U ⊓ W) := (U ⊓ W).nontrivial_iff_ne_bot.mpr hne
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(U ⊓ W))
  have hxne : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  exact (centralizer_le (Set.singleton_subset_iff.mpr x.property.1)).trans
    (hcent x x.property.2 hxne)

/-- Failure of centralizer containment forces a lower bound on relative index.
For elementary abelian subgroups, taking base-`p` ranks gives the corresponding
codimension bound. -/
public theorem card_le_relIndex_of_centralizer_not_le
    (M U W V : Subgroup G) [Finite V] (hWV : W ≤ V)
    (hcent : ∀ x ∈ W, x ≠ 1 → centralizer ({x} : Set G) ≤ M)
    (hnot : ¬ centralizer (U : Set G) ≤ M) : Nat.card W ≤ U.relIndex V := by
  by_contra h
  exact hnot (centralizer_le_of_relIndex_lt_card M U W V hWV (lt_of_not_ge h) hcent)

end Subgroup
