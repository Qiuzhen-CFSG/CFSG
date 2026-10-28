module
public import Theory.GroupTheory.SubgroupProductCard
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# A cubic lift supplementing a normal subgroup

Suppose a normal subgroup K and a subgroup B generate a finite group,
and a prescribed Sylow two-subgroup has index three in B. An order-three
subgroup disjoint from K and permuting with that Sylow supplements K.
In the quotient by K the Sylow index divides three; the disjoint cubic
image and its permuting product give the reverse order bound.

Source application: Aschbacher--Smith 13.2.7, printed pp.883--884,
where the normal subgroup is the component lift and B is the H vertex.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An order-three lift disjoint from a normal subgroup supplements it
with the prescribed Sylow when a second supplement has Sylow index three. -/
theorem normal_cubic_sylow_supplement (K B Y : Subgroup G) [K.Normal]
    (S : Sylow 2 G) (hcover : K ⊔ B = ⊤) (hSB : (S : Subgroup G) ≤ B)
    (hi : (S : Subgroup G).relIndex B = 3)
    (hc : Nat.card Y = 3) (hd : Disjoint Y K)
    (hp : (Y : Set G) * (S : Set G) = (S : Set G) * (Y : Set G)) :
    K ⊔ (Y ⊔ (S : Subgroup G)) = ⊤ := by
  let q := QuotientGroup.mk' K
  let A := Y.map q
  let P := (S : Subgroup G).map q
  let f := q.comp B.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have h := congrArg (Subgroup.map q) hcover
    simpa only [f,q,MonoidHom.range_comp,range_subtype,Subgroup.map_sup,
      QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] using h
  have hmap : ((S : Subgroup G).subgroupOf B).map f = P := by
    rw [show f = q.comp B.subtype from rfl,←map_map,map_subgroupOf_eq_of_le hSB]
  have hiP : P.index ∣ 3 := by
    have h := ((S : Subgroup G).subgroupOf B).index_map_dvd hf
    rwa [hmap,show ((S : Subgroup G).subgroupOf B).index = 3 from hi] at h
  have hinj : Function.Injective (q.subgroupMap Y) := by
    apply (injective_iff_map_eq_one _).mpr
    intro y hy
    have hk : (y : G) ∈ K := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hy)
    exact Subtype.ext (mem_bot.mp ((disjoint_iff.mp hd).le ⟨y.property,hk⟩))
  have hcA : Nat.card A = 3 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap Y)
      ⟨hinj,q.subgroupMap_surjective Y⟩).toEquiv).symm.trans hc
  have hP : IsPGroup 2 P := S.isPGroup'.map q
  have hAP : Disjoint A P := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hcA,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hperm : (A : Set (G ⧸ K)) * P = (P : Set (G ⧸ K)) * A := by
    have h := congrArg (Set.image q) hp
    simpa only [Set.image_mul,A,P,coe_map,Sylow.coe_coe] using h
  have hcard := card_set_mul_mul_card_inf A P
  rw [hAP.eq_bot,card_bot,mul_one,←coe_sup_of_set_mul_comm A P hperm,hcA] at hcard
  change Nat.card (A ⊔ P : Subgroup (G ⧸ K)) = _ at hcard
  have htop : A ⊔ P = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top,hcard,←P.index_mul_card]
    exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by decide : 0 < 3) hiP)
  have hm : (K ⊔ (Y ⊔ (S : Subgroup G))).map q = ⊤ := by
    simpa only [Subgroup.map_sup,q,QuotientGroup.map_mk'_self,bot_sup_eq] using htop
  have hh := congrArg (Subgroup.comap q) hm
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top,
    sup_eq_left.mpr (show K ≤ K ⊔ (Y ⊔ (S : Subgroup G)) from le_sup_left)] using hh
end Subgroup
