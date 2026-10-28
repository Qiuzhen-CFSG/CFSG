module
public import ABG.Recognition.ThreeMathieuEvenClasses
public import ABG.Recognition.ThreeLinearEvenData
public import Theory.GroupTheory.PrimeOrderCensus
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Mathlib.GroupTheory.Transfer

/-!
# The four order-thirteen classes in Wong's linear alternative

For a simple group of order 5616 with the characteristic-three local data,
Sylow arithmetic leaves 1, 27 or 144 Sylow 13-subgroups. Simplicity excludes 1.
The involution centralizer order excludes an even centralizer of a Sylow
13-subgroup; its automorphism group then excludes 27. Burnside transfer excludes
a centralizer equal to the remaining normalizer of order 39. Hence each
centralizer has order 13. Counting the generators of the 144 Sylow subgroups
and applying the class-size formula gives four classes of size 432.

Source: Wong (1964), Appendix (b), p.108, DOI 10.1017/S1446788700022771.
-/

open Subgroup
namespace ABG
noncomputable section
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
omit [IsSimpleGroup G] in
private theorem sylow13_centralizer_odd
    (hG : Nat.card G = 5616)
    (hInv : ∀ t : G, orderOf t = 2 → Nat.card (centralizer ({t} : Set G)) = 48)
    (P : Sylow 13 G) : ¬ 2 ∣ Nat.card (centralizer (P : Set G)) := by
  intro h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h
  have ht' : orderOf (t : G) = 2 := by simpa using ht
  have hle : (P : Subgroup G) ≤ centralizer ({(t : G)} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact mem_centralizer_iff.mp t.property x hx
  have hd := card_dvd_of_le hle
  rw [threeLinear_sylow_thirteen_card hG P, hInv _ ht'] at hd
  norm_num at hd

omit [IsSimpleGroup G] in
private theorem sylow13_count_options (hG : Nat.card G = 5616) (P : Sylow 13 G) :
    Nat.card (Sylow 13 G) = 1 ∨ Nat.card (Sylow 13 G) = 27 ∨
      Nat.card (Sylow 13 G) = 144 := by
  have hi := P.index_mul_card
  rw [threeLinear_sylow_thirteen_card hG P, hG] at hi
  have hi' : P.index = 432 := by omega
  have hd := P.card_dvd_index
  rw [hi'] at hd
  have hm := card_sylow_modEq_one 13 G
  have hb : Nat.card (Sylow 13 G) ≤ 432 := Nat.le_of_dvd (by decide) hd
  have hm' : Nat.card (Sylow 13 G) % 13 = 1 := hm
  have he : 13 * (Nat.card (Sylow 13 G) / 13) + 1 = Nat.card (Sylow 13 G) := by omega
  have arith : ∀ k : Fin 34, (13 * k.val + 1) ∣ 432 →
      k.val = 0 ∨ k.val = 2 ∨ k.val = 11 := by decide
  have hk := arith ⟨Nat.card (Sylow 13 G) / 13, by omega⟩ (he ▸ hd)
  dsimp at hk
  omega

private theorem sylow13_count_ne_one (hG : Nat.card G = 5616) (P : Sylow 13 G) :
    Nat.card (Sylow 13 G) ≠ 1 := by
  intro h
  have : Subsingleton (Sylow 13 G) := (Nat.card_eq_one_iff_unique.mp h).1
  have hnorm := P.normal_of_subsingleton
  have hp := threeLinear_sylow_thirteen_card hG P
  rcases hnorm.eq_bot_or_eq_top with he | he
  · change Nat.card (P : Subgroup G) = 13 at hp
    rw [he, card_bot] at hp
    omega
  · change Nat.card (P : Subgroup G) = 13 at hp
    rw [he, card_top, hG] at hp
    omega

omit [IsSimpleGroup G] in
private theorem sylow13_aut_index (hG : Nat.card G = 5616) (P : Sylow 13 G) :
    (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) ∣ 12 := by
  have : IsCyclic P := isCyclic_of_prime_card (threeLinear_sylow_thirteen_card hG P)
  have key := card_dvd_of_injective _
    (QuotientGroup.kerLift_injective (P : Subgroup G).normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex, IsCyclic.card_mulAut,
    threeLinear_sylow_thirteen_card hG P] at key
  norm_num at key ⊢
  exact key

private theorem sylow13_normalizer_card (hG : Nat.card G = 5616)
    (hInv : ∀ t : G, orderOf t = 2 → Nat.card (centralizer ({t} : Set G)) = 48)
    (P : Sylow 13 G) : Nat.card (normalizer (P : Set G)) = 39 := by
  have hp := threeLinear_sylow_thirteen_card hG P
  have : IsCyclic P := isCyclic_of_prime_card hp
  have hpc : (P : Subgroup G) ≤ centralizer (P : Set G) := le_centralizer _
  have hcn := centralizer_le_normalizer (P : Set G)
  have hn := (normalizer (P : Set G)).index_mul_card
  rw [← P.card_eq_index_normalizer, hG] at hn
  rcases sylow13_count_options hG P with h | h | h
  · exact False.elim (sylow13_count_ne_one hG P h)
  · rw [h] at hn
    have hn' : Nat.card (normalizer (P : Set G)) = 208 := by omega
    have hcd := card_dvd_of_le hcn
    rw [hn'] at hcd
    have hpd := card_dvd_of_le hpc
    rw [hp] at hpd
    have ho := sylow13_centralizer_odd hG hInv P
    have hc : Nat.card (centralizer (P : Set G)) = 13 := by
      have hb : Nat.card (centralizer (P : Set G)) ≤ 208 := Nat.le_of_dvd (by decide) hcd
      have he : 13 * (Nat.card (centralizer (P : Set G)) / 13) =
          Nat.card (centralizer (P : Set G)) := by omega
      have arith : ∀ k : Fin 17, (13 * k.val) ∣ 208 → ¬ 2 ∣ (13 * k.val) →
          13 * k.val = 13 := by decide
      have hk := arith ⟨Nat.card (centralizer (P : Set G)) / 13, by omega⟩
        (he ▸ hcd) (he ▸ ho)
      dsimp at hk
      omega
    have hi := (centralizer (P : Set G) |>.subgroupOf (normalizer (P : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hcn).toEquiv, hc, hn'] at hi
    change (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) * 13 = 208 at hi
    have hd := sylow13_aut_index hG P
    have hie : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 16 := by omega
    rw [hie] at hd
    norm_num at hd
  · rw [h] at hn
    omega

private theorem sylow13_centralizer_card (hG : Nat.card G = 5616)
    (hInv : ∀ t : G, orderOf t = 2 → Nat.card (centralizer ({t} : Set G)) = 48)
    (P : Sylow 13 G) : Nat.card (centralizer (P : Set G)) = 13 := by
  have hp := threeLinear_sylow_thirteen_card hG P
  have : IsCyclic P := isCyclic_of_prime_card hp
  have hpc : (P : Subgroup G) ≤ centralizer (P : Set G) := le_centralizer _
  have hcn := centralizer_le_normalizer (P : Set G)
  have hn := sylow13_normalizer_card hG hInv P
  have hcd := card_dvd_of_le hcn
  rw [hn] at hcd
  have hpd := card_dvd_of_le hpc
  rw [hp] at hpd
  have hc : Nat.card (centralizer (P : Set G)) = 13 ∨
      Nat.card (centralizer (P : Set G)) = 39 := by
    have arith : ∀ n : Fin 40, n.val ∣ 39 → 13 ∣ n.val →
        n.val = 13 ∨ n.val = 39 := by decide
    exact arith ⟨_, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hcd)⟩ hcd hpd
  rcases hc with hc | hc
  · exact hc
  have he : centralizer (P : Set G) = normalizer (P : Set G) :=
    eq_of_le_of_card_ge hcn (by omega)
  have hnle : normalizer (P : Set G) ≤ centralizer (P : Set G) := he.ge
  have hk := MonoidHom.ker_transferSylow_isComplement' P hnle
  have hprod := hk.card_mul_card
  rw [hp, hG] at hprod
  rcases (inferInstance : (MonoidHom.transferSylow P hnle).ker.Normal).eq_bot_or_eq_top with he | he
  · rw [he, card_bot] at hprod
    omega
  · rw [he, card_top, hG] at hprod
    omega

variable (c : ThreeGlobalDegreeData G)
include c

private theorem involution_centralizer_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (t : G) (ht : orderOf t = 2) : Nat.card (centralizer ({t} : Set G)) = 48 := by
  simpa only [ht, ite_true] using c.even_centralizer_card S hS t (by rw [ht])

/-- In the linear alternative the Sylow-thirteen normalizer has order 39. -/
public theorem ThreeGlobalDegreeData.linear_sylow_thirteen_normalizer_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (P : Sylow 13 G) :
    Nat.card (normalizer (P : Set G)) = 39 :=
  sylow13_normalizer_card hG (involution_centralizer_card c S hS) P

/-- In the linear alternative the Sylow-thirteen centralizer has order 13. -/
public theorem ThreeGlobalDegreeData.linear_sylow_thirteen_centralizer_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (P : Sylow 13 G) :
    Nat.card (centralizer (P : Set G)) = 13 :=
  sylow13_centralizer_card hG (involution_centralizer_card c S hS) P

/-- There are 144 Sylow-thirteen subgroups in the linear alternative. -/
public theorem ThreeGlobalDegreeData.linear_sylow_thirteen_count
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) : Nat.card (Sylow 13 G) = 144 := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 13) (G := G)
  have hn := (normalizer (P : Set G)).index_mul_card
  rw [← P.card_eq_index_normalizer,
    c.linear_sylow_thirteen_normalizer_card S hS hG P, hG] at hn
  omega

/-- Every element of order 13 has centralizer order 13. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_element_centralizer_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (x : G) (hx : orderOf x = 13) :
    Nat.card (centralizer ({x} : Set G)) = 13 := by
  obtain ⟨P, hPx⟩ := Sylow.exists_mem_of_orderOf_eq hx
  have hP := P.zpowers_eq_of_card_eq (threeLinear_sylow_thirteen_card hG P) hx hPx
  have he : centralizer ({x} : Set G) = centralizer (P : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure, hP]
    rfl
  rw [he]
  exact c.linear_sylow_thirteen_centralizer_card S hS hG P

/-- No element order is a proper multiple of 13. -/
public theorem ThreeGlobalDegreeData.linear_order_eq_thirteen_of_dvd
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (x : G) (hx : 13 ∣ orderOf x) : orderOf x = 13 := by
  let y := x ^ (orderOf x / 13)
  have hy : orderOf y = 13 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hx
  have hm : x ∈ centralizer ({y} : Set G) :=
    mem_centralizer_singleton_iff.mpr (Commute.self_pow x _).eq
  have hd := (centralizer ({y} : Set G)).orderOf_dvd_natCard hm
  rw [c.linear_thirteen_element_centralizer_card S hS hG y hy] at hd
  exact Nat.dvd_antisymm hd hx

/-- The 144 Sylow-thirteen subgroups contribute 1728 elements of order 13. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_element_count
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) : Nat.card {x : G // orderOf x = 13} = 1728 := by
  rw [Sylow.card_orderOf_eq_of_card (threeLinear_sylow_thirteen_card hG),
    c.linear_sylow_thirteen_count S hS hG]

/-- Every order-thirteen conjugacy class has size 432. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_class_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (x : G) (hx : orderOf x = 13) :
    Nat.card (ConjClasses.mk x).carrier = 432 := by
  have h := ConjClasses.nat_card_carrier_mul_card_centralizer x
  rw [c.linear_thirteen_element_centralizer_card S hS hG x hx, hG] at h
  omega

omit c [IsSimpleGroup G] in
/-- The finite set of actual order-thirteen conjugacy classes. -/
public def threeLinearThirteenClasses (G : Type*) [Group G] [Finite G] : Finset (ConjClasses G) :=
  ConjClasses.ofOrder G 13

omit c [IsSimpleGroup G] in
/-- Membership is exactly order thirteen, with no chosen or assumed class table. -/
@[simp] public theorem mem_threeLinearThirteenClasses (x : G) :
    ConjClasses.mk x ∈ threeLinearThirteenClasses G ↔ orderOf x = 13 :=
  ConjClasses.mk_mem_ofOrder 13 x

open scoped BigOperators

/-- Every carrier in the actual thirteen-class finset has cardinality 432. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_carrier_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) (k : ConjClasses G) (hk : k ∈ threeLinearThirteenClasses G) :
    Nat.card k.carrier = 432 := by
  obtain ⟨x, rfl, hx⟩ := (ConjClasses.mem_ofOrder_iff 13 k).mp hk
  exact c.linear_thirteen_class_card S hS hG x hx

/-- The carrier-cardinality sum counts precisely the order-thirteen elements. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_class_sum
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) :
    ∑ k ∈ threeLinearThirteenClasses G, Nat.card k.carrier = 1728 := by
  rw [threeLinearThirteenClasses, ConjClasses.sum_card_ofOrder,
    c.linear_thirteen_element_count S hS hG]

/-- There are exactly four actual conjugacy classes of order-thirteen elements. -/
public theorem ThreeGlobalDegreeData.linear_thirteen_classes_card
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616) : (threeLinearThirteenClasses G).card = 4 := by
  have h := c.linear_thirteen_class_sum S hS hG
  have he : (∑ k ∈ threeLinearThirteenClasses G, Nat.card k.carrier) =
      (threeLinearThirteenClasses G).card * 432 := by
    calc
      _ = ∑ _k ∈ threeLinearThirteenClasses G, 432 :=
        Finset.sum_congr rfl (fun k hk => c.linear_thirteen_carrier_card S hS hG k hk)
      _ = _ := by simp
  omega

end
end ABG
