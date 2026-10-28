module

public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Normal intersections of coprime subgroup products

For subgroups A and P of coprime orders and a normal subgroup I, an element
of AP lying in I has both factors in I. Indeed, the images of A and P in
G/I have coprime orders and hence trivial intersection. When AP = PA this
identifies the intersection of their join with I and computes its order.

A related quotient argument shows that a homomorphism with an r-group
kernel preserves the intersection of a p-group A with a normal subgroup J
when p and r are coprime. Projection modulo J detects the kernel factor;
injectivity on A then preserves the intersection's cardinality.

The final application retains the literal quotient by O₂(G): a cubic
intersection of order three and a Sylow intersection of order sixteen
give an intersection of order forty-eight. This is the subgroup-order
calculation in the PSU₃(5) case of Aschbacher–Smith, Proposition 9.3.1,
printed pp.732–733.
-/

open scoped Pointwise

namespace Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- A normal intersection passes through a map on a prime subgroup when
the kernel is a group for a coprime prime. -/
public theorem map_inf_map_eq_of_coprime_pKernel
    (f : G →* H) (A J : Subgroup G) [J.Normal]
    {p r : ℕ} (hA : IsPGroup p A) (hk : IsPGroup r f.ker) (hcop : Nat.Coprime p r) :
    A.map f ⊓ J.map f = (A ⊓ J).map f := by
  apply le_antisymm _ (map_inf_le A J f)
  rintro y ⟨⟨a, ha, rfl⟩, hj⟩
  refine mem_map.mpr ⟨a, ⟨ha, ?_⟩, rfl⟩
  let q := QuotientGroup.mk' J
  have ha_sup : a ∈ J ⊔ f.ker := by
    rw [← comap_map_eq]
    exact hj
  have hqa : q a ∈ f.ker.map q := by
    have hh := mem_map_of_mem q ha_sup
    simpa only [map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq] using hh
  have hq_one : q a = 1 :=
    disjoint_def.mp ((hA.map q).disjoint_of_coprime (hk.map q) hcop)
      (mem_map_of_mem q ha) hqa
  exact (QuotientGroup.eq_one_iff a).mp hq_one

/-- A coprime prime-group kernel preserves the order of the intersection
of a prime subgroup with a normal subgroup. -/
public theorem card_map_inf_map_of_coprime_pKernel
    (f : G →* H) (A J : Subgroup G) [J.Normal]
    {p r : ℕ} (hA : IsPGroup p A) (hk : IsPGroup r f.ker) (hcop : Nat.Coprime p r) :
    Nat.card (A.map f ⊓ J.map f : Subgroup H) = Nat.card (A ⊓ J : Subgroup G) := by
  rw [map_inf_map_eq_of_coprime_pKernel f A J hA hk hcop]
  let g := f.subgroupMap (A ⊓ J)
  have hi : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp (hA.disjoint_of_coprime hk hcop) x.property.1
      (congrArg Subtype.val hx)
  exact (Nat.card_congr (MulEquiv.ofBijective g
    ⟨hi, f.subgroupMap_surjective (A ⊓ J)⟩).toEquiv).symm

/-- Intersecting a product of coprime subgroups with a normal subgroup
intersects both factors. Permutability is not required for this set equality. -/
public theorem set_mul_inter_normal_of_coprime [Finite G]
    (A P I : Subgroup G) [I.Normal]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card P)) :
    ((A : Set G) * (P : Set G)) ∩ I =
      (↑(A ⊓ I) : Set G) * (↑(P ⊓ I) : Set G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨a, ha, p, hp, rfl⟩, hi⟩
    let q := QuotientGroup.mk' I
    have hd : Disjoint (A.map q) (P.map q) :=
      disjoint_of_coprime_natCard (hcop.of_dvd (A.card_map_dvd q) (P.card_map_dvd q))
    have hmul : q a * q p = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff (a * p)).mpr hi
    have heq : q a = (q p)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have ha_one : q a = 1 := disjoint_def.mp hd (mem_map_of_mem q ha) (by
      rw [heq]
      exact (P.map q).inv_mem (mem_map_of_mem q hp))
    have hp_one : q p = 1 := by simpa only [ha_one, one_mul] using hmul
    exact Set.mem_mul.mpr ⟨a, ⟨ha, (QuotientGroup.eq_one_iff a).mp ha_one⟩,
      p, ⟨hp, (QuotientGroup.eq_one_iff p).mp hp_one⟩, rfl⟩
  · rintro x ⟨a, ha, p, hp, rfl⟩
    exact ⟨Set.mul_mem_mul ha.1 hp.1, I.mul_mem ha.2 hp.2⟩

/-- The normal intersection of a permutable coprime join has the product
of the two intersection orders. -/
public theorem card_subgroupOf_sup_of_coprime_permutable [Finite G]
    (A P I : Subgroup G) [I.Normal]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hperm : (A : Set G) * (P : Set G) = (P : Set G) * (A : Set G)) :
    Nat.card ((A ⊔ P).subgroupOf I) =
      Nat.card (A ⊓ I : Subgroup G) * Nat.card (P ⊓ I : Subgroup G) := by
  have hset : (↑((A ⊔ P) ⊓ I) : Set G) =
      (↑(A ⊓ I) : Set G) * (↑(P ⊓ I) : Set G) := by
    rw [coe_inf, coe_sup_of_set_mul_comm A P hperm, set_mul_inter_normal_of_coprime A P I hcop]
  have hd : Disjoint (A ⊓ I) (P ⊓ I) :=
    (disjoint_of_coprime_natCard hcop).mono inf_le_left inf_le_left
  have hc := card_set_mul_mul_card_inf (A ⊓ I) (P ⊓ I)
  rw [← hset, hd.eq_bot, card_bot, mul_one] at hc
  rw [← inf_subgroupOf_right (A ⊔ P) I,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : (A ⊔ P) ⊓ I ≤ I)).toEquiv]
  exact hc

/-- The literal two-core quotient preserves a three-group's intersection
order with a normal subgroup. -/
public theorem card_map_inf_map_twoCore_of_isThreeGroup
    (A J : Subgroup G) [J.Normal] (hA : IsPGroup 3 A) :
    let q := QuotientGroup.mk' (pCore 2 G)
    Nat.card (A.map q ⊓ J.map q : Subgroup (G ⧸ pCore 2 G)) =
      Nat.card (A ⊓ J : Subgroup G) := by
  apply card_map_inf_map_of_coprime_pKernel _ A J hA (r := 2)
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · decide

/-- In the literal two-core quotient, the cubic and sixteen-element
Sylow intersections give the order-forty-eight subgroup used in local control. -/
public theorem card_subgroupOf_sup_twoCore_eq_fortyEight [Finite G]
    (A J : Subgroup G) [J.Normal] (hA : IsPGroup 3 A)
    (P : Sylow 2 (G ⧸ pCore 2 G))
    (hperm : (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)) *
        (P : Set (G ⧸ pCore 2 G)) =
      (P : Set (G ⧸ pCore 2 G)) *
        (A.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G)))
    (hAJ : Nat.card (A ⊓ J : Subgroup G) = 3)
    (hPJ : Nat.card ((P : Subgroup (G ⧸ pCore 2 G)) ⊓
      J.map (QuotientGroup.mk' (pCore 2 G)) : Subgroup (G ⧸ pCore 2 G)) = 16) :
    Nat.card ((A.map (QuotientGroup.mk' (pCore 2 G)) ⊔
      (P : Subgroup (G ⧸ pCore 2 G))).subgroupOf
        (J.map (QuotientGroup.mk' (pCore 2 G)))) = 48 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (J.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hcop : Nat.Coprime (Nat.card (A.map q))
      (Nat.card (P : Subgroup (G ⧸ pCore 2 G))) := by
    obtain ⟨a, ha⟩ := (hA.map q).exists_card_eq
    obtain ⟨b, hb⟩ := P.isPGroup'.exists_card_eq
    rw [ha, hb]
    exact (by decide : Nat.Coprime 3 2).pow a b
  rw [card_subgroupOf_sup_of_coprime_permutable _ _ _ hcop hperm,
    card_map_inf_map_twoCore_of_isThreeGroup A J hA, hAJ, hPJ]

end Subgroup
