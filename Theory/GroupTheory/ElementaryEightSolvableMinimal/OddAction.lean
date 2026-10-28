module
public import Theory.GroupTheory.ElementaryEightSolvableMinimal
public import Theory.GroupTheory.ElementaryEightCoreFreeAction

/-!
# Odd solvable irreducible actions on an elementary eight

An irreducible automizer has trivial two-core. If it had even order, the
solvable core-free automizer theorem would give order six, contradicting the
seven-free irreducibility obstruction. Thus every two-subgroup of an actor
centralizes a minimal invariant elementary eight. When the eight lies in
that two-subgroup, its order is bounded by the center's order.

The application is the whole solvable Cartan actor in J₄ in
Aschbacher--Smith 5.1.13, printed p.637: its full Sylow has center of order
two, excluding every minimal elementary-eight row, including the first pure
row. No restriction on the actor's odd prime divisors is assumed.
-/

public noncomputable section
namespace Theory.GroupTheory
open Subgroup
private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A solvable irreducible elementary-eight automizer has odd order. -/
theorem odd_card_of_solvable_irreducible_elementary_eight
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) [Group.IsSolvable A]
    (hirr : ∀ D : Subgroup E, (∀ a : A, ∀ x : E, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤) : Odd (Nat.card A) := by
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE]; decide)
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hc := card_eq_six_of_elementary_eight_automorphisms_twoCore_eq_bot hE A
    (irreducible_range_two_core_eq_bot A hirr) (even_iff_two_dvd.mp heven)
  exact not_irreducible_solvable_elementary_eight hE A (by rw [hc]; decide) hirr

/-- Two-subgroups centralize an elementary eight minimal under a solvable actor. -/
theorem centralizes_of_solvable_minimal_elementary_eight
    {G : Type*} [Group G] [Finite G] (K A P : Subgroup G)
    [Group.IsSolvable K] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hn : K ≤ normalizer (A : Set G))
    (hmin : ∀ X : Subgroup G, X ≤ A → K ≤ normalizer (X : Set G) → X = ⊥ ∨ X = A)
    (hPK : P ≤ K) (hp : IsPGroup 2 P) : P ≤ centralizer (A : Set G) := by
  let f := A.normalizerMonoidHom.comp (inclusion hn)
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hirr : ∀ D : Subgroup A, (∀ a : f.range, ∀ x : A, x ∈ D → a • x ∈ D) →
      D = ⊥ ∨ D = ⊤ := by
    intro D hD
    have hnD : K ≤ normalizer (D.map A.subtype : Set G) := by
      intro k hk
      apply mem_normalizer_iff.mpr
      intro x
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨f ⟨k,hk⟩ a,hD ⟨f ⟨k,hk⟩,⟨⟨k,hk⟩,rfl⟩⟩ a ha,rfl⟩
      · rintro ⟨a,ha,he⟩
        refine ⟨f ⟨k⁻¹,K.inv_mem hk⟩ a,
          hD ⟨f ⟨k⁻¹,K.inv_mem hk⟩,⟨⟨k⁻¹,K.inv_mem hk⟩,rfl⟩⟩ a ha,?_⟩
        change k⁻¹ * (a : G) * (k⁻¹)⁻¹ = x
        change (a : G) = k * x * k⁻¹ at he
        rw [he,inv_inv]
        group
    rcases hmin (D.map A.subtype) (map_subtype_le D) hnD with hh | hh
    · exact Or.inl ((D.map_eq_bot_iff_of_injective A.subtype_injective).mp hh)
    · apply Or.inr
      apply Subgroup.map_injective A.subtype_injective
      rw [hh,←MonoidHom.range_eq_map,A.range_subtype]
  have ho := odd_card_of_solvable_irreducible_elementary_eight hA f.range hirr
  let g := f.rangeRestrict.comp (inclusion hPK)
  have hp' : IsPGroup 2 g.range := hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hg : g.range = ⊥ := by
    apply card_eq_one.mp
    exact hp'.card_eq_or_dvd.resolve_right
      (ho.not_two_dvd_nat ∘ (fun hh => hh.trans g.range.card_subgroup_dvd_card))
  intro p hp
  have hgp : g ⟨p,hp⟩ = 1 := mem_bot.mp (hg ▸ (show g ⟨p,hp⟩ ∈ g.range from ⟨⟨p,hp⟩,rfl⟩))
  have hf : f ⟨p,hPK hp⟩ = 1 := congrArg Subtype.val hgp
  have hk : inclusion hn ⟨p,hPK hp⟩ ∈ A.normalizerMonoidHom.ker := hf
  rwa [normalizerMonoidHom_ker] at hk


/-- A contained minimal elementary eight embeds in the two-subgroup center. -/
theorem card_le_center_of_solvable_minimal_elementary_eight
    {G : Type*} [Group G] [Finite G] (K A P : Subgroup G)
    [Group.IsSolvable K] [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hn : K ≤ normalizer (A : Set G))
    (hmin : ∀ X : Subgroup G, X ≤ A → K ≤ normalizer (X : Set G) → X = ⊥ ∨ X = A)
    (hPK : P ≤ K) (hp : IsPGroup 2 P) (hAP : A ≤ P) :
    Nat.card A ≤ Nat.card (center P) := by
  have hPC := centralizes_of_solvable_minimal_elementary_eight K A P hA hn hmin hPK hp
  have hAc : A.subgroupOf P ≤ center P := by
    intro a ha
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext ((hPC p.property) a ha).symm
  have hc : Nat.card (A.subgroupOf P) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv
  exact hc ▸ card_le_of_le hAc

end Theory.GroupTheory
