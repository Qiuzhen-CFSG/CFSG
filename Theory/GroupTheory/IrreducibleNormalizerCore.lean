module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Irreducible p-subgroups and the normalizer's p-core

A nontrivial normal p-subgroup meets the center of the ambient p-core.
Irreducibility makes its entire module centralize that core. If the module
is self-centralizing in a specified overgroup, the overgroup's intersection
with the normalizer's p-core is therefore exactly the module.

The ambient formulation retains the literal subgroup embeddings. It is used
in Aschbacher–Smith, Lemma 14.4.9, printed p.1010 of `refs/quasithin.pdf`.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A minimal normal p-subgroup is centralized by the p-core. -/
public theorem pCore_le_centralizer_of_minimal_normal_pSubgroup {p : ℕ} [Fact p.Prime]
    (D : Subgroup G) [D.Normal] (hp : IsPGroup p D)
    (hirr : ∀ E : Subgroup G, E ≤ D → E.Normal → E = ⊥ ∨ E = D) :
    pCore p G ≤ centralizer (D : Set G) := by
  by_cases hD : D = ⊥
  · subst D
    intro x hx y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  let Q := pCore p G
  have hDQ : D ≤ Q := le_sSup ⟨inferInstance, hp⟩
  have hnon : D.subgroupOf Q ≠ ⊥ := by
    intro he
    have hh := congrArg (fun E : Subgroup Q => E.map Q.subtype) he
    rw [map_subgroupOf_eq_of_le hDQ, map_bot] at hh
    exact hD hh
  have hmeet := center_inf_ne_bot_of_normal (show IsPGroup p Q from pCore_isPGroup)
    (D.subgroupOf Q) hnon
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  let C := D ⊓ centralizer (Q : Set G)
  have hC : C ≠ ⊥ := by
    intro he
    have hxc : (x.val : G) ∈ C := by
      refine ⟨x.property.2, ?_⟩
      intro y hy
      exact congrArg Subtype.val ((mem_center_iff.mp x.property.1) ⟨y, hy⟩)
    have hx1 : (x.val : G) = 1 := by simpa [he] using hxc
    exact hx (Subtype.ext (Subtype.ext hx1))
  have hCD : C = D := (hirr C inf_le_left inferInstance).resolve_left hC
  exact le_centralizer_iff.mp (hCD ▸ (show C ≤ centralizer (Q : Set G) from inf_le_right))

/-- An irreducible normalizing action forces the overgroup's p-core to centralize the module. -/
public theorem pCoreIn_le_centralizer_of_irreducible {p : ℕ} [Fact p.Prime]
    (D Y N : Subgroup G) (hp : IsPGroup p D) (hDN : D ≤ N)
    (hND : N ≤ normalizer (D : Set G)) (hYN : Y ≤ N)
    (hirr : ∀ E : Subgroup G, E ≤ D → Y ≤ normalizer (E : Set G) →
      E = ⊥ ∨ E = D) :
    N.pCoreIn p ≤ centralizer (D : Set G) := by
  let D' := D.subgroupOf N
  let : D'.Normal := (normal_subgroupOf_iff_le_normalizer hDN).mpr hND
  have hminimal (E : Subgroup N) (hE : E ≤ D') (hn : E.Normal) : E = ⊥ ∨ E = D' := by
    have hED : E.map N.subtype ≤ D := by
      simpa only [D', map_subgroupOf_eq_of_le hDN] using map_mono (f := N.subtype) hE
    have hnorm : N ≤ normalizer (E.map N.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      intro g hg x hx
      obtain ⟨x, hx, rfl⟩ := hx
      exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hn.conj_mem x hx ⟨g, hg⟩, rfl⟩
    rcases hirr (E.map N.subtype) hED (hYN.trans hnorm) with he | he
    · exact Or.inl ((E.map_eq_bot_iff_of_injective N.subtype_injective).mp he)
    · apply Or.inr
      apply map_injective N.subtype_injective
      simpa only [D', map_subgroupOf_eq_of_le hDN] using he
  have hc := pCore_le_centralizer_of_minimal_normal_pSubgroup D' hp.comap_subtype hminimal
  rintro q ⟨q', hq', rfl⟩ d hd
  exact congrArg Subtype.val ((hc hq') ⟨d, hDN hd⟩ hd)

/-- Self-centralization identifies the intersection with the normalizer's p-core. -/
public theorem inf_pCoreIn_normalizer_eq_of_irreducible {p : ℕ} [Fact p.Prime]
    (D U Y : Subgroup G) (hp : IsPGroup p D)
    (hYD : Y ≤ normalizer (D : Set G))
    (hirr : ∀ E : Subgroup G, E ≤ D → Y ≤ normalizer (E : Set G) →
      E = ⊥ ∨ E = D)
    (hself : (U ⊔ D) ⊓ centralizer (D : Set G) = D) :
    (U ⊔ D) ⊓ (normalizer (D : Set G)).pCoreIn p = D := by
  have hcore := pCoreIn_le_centralizer_of_irreducible D Y (normalizer (D : Set G)) hp
    D.le_normalizer le_rfl hYD hirr
  apply le_antisymm
  · exact (inf_le_inf_left _ hcore).trans (le_of_eq hself)
  · exact le_inf le_sup_right (le_pCoreIn_of_normalizes hp D.le_normalizer le_rfl)


end Subgroup
