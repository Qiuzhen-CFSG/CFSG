module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Index

/-!
# Fixed points of pairs of conjugate p-subgroups

A p-subgroup contained in the p-core of an element centralizer generates a
p-group with every p-subgroup fixing that element. This yields a fixed-point
criterion for pairs of conjugates. We transport that criterion by the actual
conjugation maps and force a fixed point when a subgroup is larger than the
index of the relevant centralizer.

These are the group-theoretic steps in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined 1 March 2004 manuscript, Lemma 12.7.22(5)
and the final contradiction on printed pp.848–849 (PDF pp.865–866).
The source's core containments and numerical configuration remain inputs.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- A subgroup larger than the number of cosets cannot avoid the subgroup defining
that index. The index is taken in the actual overgroup `D`. -/
public theorem inf_ne_bot_of_relIndex_lt_card [Finite G]
    {A B C D : Subgroup G} (hBA : B ≤ A) (hBD : B ≤ D)
    (hcard : C.relIndex D < Nat.card B) : A ⊓ C ≠ ⊥ := by
  intro hbot
  have hBC : B ⊓ C = ⊥ := le_bot_iff.mp ((inf_le_inf_right C hBA).trans hbot.le)
  have heq : C.relIndex B = Nat.card B := by
    rw [← inf_relIndex_left, hBC, relIndex_bot_left]
  have hle := C.relIndex_le_of_le_right hBD ((show Nat.card (D ⧸ C.subgroupOf D) ≠ 0 from Nat.card_pos.ne'))
  rw [heq] at hle
  exact (not_lt_of_ge hle) hcard

/-- If `V` lies in the local p-core at `v`, adjoining a p-subgroup fixing `v`
still gives a p-group. The core is normal only in that element centralizer. -/
public theorem isPGroup_sup_of_elementCentralizer_core {p : ℕ} {V A : Subgroup G}
    {v : G} (hA : IsPGroup p A)
    (hcore : V ≤ (centralizer ({v} : Set G)).pCoreIn p)
    (hfix : v ∈ centralizer (A : Set G)) : IsPGroup p (V ⊔ A : Subgroup G) := by
  let H : Subgroup G := centralizer ({v} : Set G)
  have hAH : A ≤ H := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hfix a ha)
  have hnorm : H ≤ normalizer (H.pCoreIn p : Set G) := by
    have hn := (pCore p H).le_normalizer_map H.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  exact ((isPGroup_pCoreIn p H).to_sup_of_normal_left' hA (hAH.trans hnorm)).to_le
    (sup_le_sup hcore le_rfl)

/-- A nonidentity common fixed point selects a local core containing `V`,
so the generated subgroup is a p-group. -/
public theorem isPGroup_sup_of_fixed_point_core {p : ℕ} {V A : Subgroup G}
    (hA : IsPGroup p A)
    (hcore : ∀ v ∈ V, v ≠ 1 → V ≤ (centralizer ({v} : Set G)).pCoreIn p)
    (hfix : V ⊓ centralizer (A : Set G) ≠ ⊥) : IsPGroup p (V ⊔ A : Subgroup G) := by
  obtain ⟨v, hv⟩ := ne_bot_iff_exists_ne_one.mp hfix
  exact isPGroup_sup_of_elementCentralizer_core hA
    (hcore v v.property.1 (fun h => hv (Subtype.ext h))) v.property.2

/-- Transport the fixed-point criterion from `V` to the literal pair
`V.conjBy g`, `(V.conjBy g).conjBy k`. The transporter back to `V`
is `g⁻¹ * k * g`, as required by left conjugation. -/
public theorem isPGroup_conjugate_pair_of_fixed_points {p : ℕ} (V : Subgroup G)
    (hpair : ∀ a : G, V ⊓ centralizer (V.conjBy a : Set G) ≠ ⊥ →
      IsPGroup p (V ⊔ V.conjBy a : Subgroup G))
    (g k : G)
    (hfix : V.conjBy g ⊓ centralizer ((V.conjBy g).conjBy k : Set G) ≠ ⊥) :
    IsPGroup p (V.conjBy g ⊔ (V.conjBy g).conjBy k : Subgroup G) := by
  let a := g⁻¹ * k * g
  have heq : (V.conjBy a).conjBy g = (V.conjBy g).conjBy k := by
    simp [a, conjBy_conjBy, mul_assoc]
  have hf : V ⊓ centralizer (V.conjBy a : Set G) ≠ ⊥ := by
    obtain ⟨v, hv⟩ := ne_bot_iff_exists_ne_one.mp hfix
    obtain ⟨w, hw, he⟩ := v.property.1
    apply ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨w, hw, ?_⟩, ?_⟩
    · intro x hx
      apply (MulAut.conj g).injective
      simp only [map_mul]
      have he' : (MulAut.conj g) w = (v : G) := he
      rw [he']
      exact mem_centralizer_iff.mp v.property.2 ((MulAut.conj g) x)
        (heq ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    · intro h
      apply hv
      apply Subtype.ext
      have hw1 : w = 1 := congrArg Subtype.val h
      simpa [hw1] using he.symm
  have hp := (hpair a hf).map (MulAut.conj g).toMonoidHom
  change IsPGroup p ((V ⊔ V.conjBy a).map (MulAut.conj g).toMonoidHom) at hp
  rw [map_sup] at hp
  change IsPGroup p (V.conjBy g ⊔ (V.conjBy a).conjBy g : Subgroup G) at hp
  rwa [heq] at hp

/-- The fixed-point criterion and a centralizer-index bound force the
generated pair of conjugates to be a p-group. -/
public theorem isPGroup_conjugate_pair_of_relIndex_lt_card [Finite G]
    {p : ℕ} (V : Subgroup G)
    (hpair : ∀ a : G, V ⊓ centralizer (V.conjBy a : Set G) ≠ ⊥ →
      IsPGroup p (V ⊔ V.conjBy a : Subgroup G))
    (g k : G) (B D : Subgroup G) (hBA : B ≤ V.conjBy g) (hBD : B ≤ D)
    (hcard : (centralizer ((V.conjBy g).conjBy k : Set G)).relIndex D < Nat.card B) :
    IsPGroup p (V.conjBy g ⊔ (V.conjBy g).conjBy k : Subgroup G) :=
  isPGroup_conjugate_pair_of_fixed_points V hpair g k
    (inf_ne_bot_of_relIndex_lt_card hBA hBD hcard)
end Subgroup
