module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ComplementAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# The four-group and faithful action in the exceptional J₁ branch

In the elementary order-27 branch, the marked prime is three. An actual
inverter in the alternating centralizer model, together with `z`, generates
a four-group normalizing the odd complement. Its fixed subgroup on the
complement is trivial by the ambient four-centralizer calculation.

The complement is self-centralizing: otherwise its centralizer would
contain an involution, whose centralizer of order 120 cannot contain a
subgroup of order 27. Thus the normalizer's literal action has kernel the
relative copy of the complement. Every involution fixes at most a line.

These are preparatory steps toward the exceptional normalizer in Bender,
*Finite groups with large subgroups* (1974), (4.1), printed p.225, citing
Janko (1966), proof of Lemma 3.1. They do not assert the order of the
normalizer action image or fusion within that image.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1CentralizerData
private abbrev M := alternatingGroup (Fin 5) × Multiplicative (ZMod 2)
private def three : M :=
  (⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)
private def reflection : M :=
  (⟨Equiv.swap 0 2 * Equiv.swap 3 4, by simp [Equiv.Perm.mem_alternatingGroup]⟩, 1)
private theorem three_order : orderOf three = 3 := by
  apply orderOf_eq_prime <;> decide +kernel
private theorem reflection_order : orderOf reflection = 2 := by
  apply orderOf_eq_prime <;> decide +kernel
private theorem reflection_inverts : reflection * three * reflection⁻¹ = three⁻¹ := by
  decide +kernel

private theorem model_inverter (x : M) (hx : orderOf x = 3) :
    ∃ t : M, orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hP (P : Sylow 3 M) : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity]
    have hc : Nat.card M = 120 := by
      rw [Nat.card_prod, nat_card_alternatingGroup]
      norm_num [Nat.factorial, Nat.card_eq_fintype_card]
    rw [hc]
    decide +kernel
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_card_eq_prime (zpowers three) three
    (mem_zpowers three) three_order hP x hx
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg
  let e := MulAut.conj g
  have hr : reflection * e x * reflection⁻¹ = (e x)⁻¹ := by
    change (MulAut.conj reflection) (e x) = (e x)⁻¹
    rw [show e x = three ^ n from hn.symm, map_zpow]
    change (reflection * three * reflection⁻¹) ^ n = _
    rw [reflection_inverts, inv_zpow]
  refine ⟨e.symm reflection, (e.symm.orderOf_eq _).trans reflection_order, ?_⟩
  apply e.injective
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hr

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The actual alternating model supplies an involution in `C_G(z)`
inverting each of its elements of order three. -/
private theorem exceptional_local_three_inverter (x : G)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3) :
    ∃ t : G, t ∈ centralizer ({h.z} : Set G) ∧ orderOf t = 2 ∧
      t * x * t⁻¹ = x⁻¹ := by
  let C := centralizer ({h.z} : Set G)
  let e := h.alternatingCentralizerEquiv
  let xC : C := ⟨x, hxC⟩
  have hx' : orderOf (e xC) = 3 := (e.orderOf_eq _).trans
    ((orderOf_injective C.subtype Subtype.val_injective xC).symm.trans hx)
  obtain ⟨u, hu, hi⟩ := model_inverter (e xC) hx'
  let t := e.symm u
  have ht : orderOf (t : G) = 2 :=
    (orderOf_injective C.subtype Subtype.val_injective t).trans
      ((e.symm.orderOf_eq _).trans hu)
  refine ⟨t, t.property, ht, ?_⟩
  have he : t * xC * t⁻¹ = xC⁻¹ := by
    apply e.injective
    simpa only [t, map_mul, map_inv, MulEquiv.apply_symm_apply] using hi
  exact congrArg Subtype.val he



/-- The order-27 branch occurs only at three, before a normalizer is constructed. -/
public theorem OddCentralizerComplement.prime_eq_three_of_card_twentySeven
    {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (hc : Nat.card A = 27)
    (p : ℕ) (hp : p = 3 ∨ p = 5) (hx : orderOf x = p) : p = 3 := by
  have hd := orderOf_dvd_natCard (⟨x, a.x_mem⟩ : A)
  have hxA : orderOf (⟨x, a.x_mem⟩ : A) = p :=
    (orderOf_injective A.subtype Subtype.val_injective ⟨x, a.x_mem⟩).symm.trans hx
  rw [hxA, hc] at hd
  rcases hp with rfl | rfl
  · rfl
  · norm_num at hd

/-- An elementary order-27 complement admits an actual ambient normalizing
four-group containing the distinguished involution. -/
public theorem OddCentralizerComplement.exists_normalizing_four_of_card_twentySeven
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A) (hc : Nat.card A = 27)
    (p : ℕ) (hp : p = 3 ∨ p = 5)
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = p) :
    ∃ V : Subgroup G, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      h.z ∈ V ∧ V ≤ normalizer (A : Set G) ∧
      A ⊓ centralizer (V : Set G) = ⊥ := by
  have hp3 := a.prime_eq_three_of_card_twentySeven hc p hp hx
  have hx3 : orderOf x = 3 := hx.trans hp3
  obtain ⟨t, htz, ht, htx⟩ := h.exceptional_local_three_inverter x hxC hx3
  have htzne : h.z ≠ t := by
    intro heq
    have hxinv : x = x⁻¹ := by
      rw [← heq, (mem_centralizer_singleton_iff.mp hxC).symm,
        mul_inv_cancel_right] at htx
      exact htx
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hxinv]
      exact inv_mul_cancel x
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx3] at hd
    norm_num at hd
  let V := closure ({h.z, t} : Set G)
  let _ : IsKleinFour V := isKleinFour_closure_pair_of_orderOf h.z t h.involution ht
    htzne (mem_centralizer_singleton_iff.mp htz).symm
  have hVe : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hVc : Nat.card V = 4 := IsKleinFour.card_four
  have htN : t ∈ normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (t * x * t⁻¹) = zpowers x
    rw [htx, zpowers_inv]
  refine ⟨V, hVe, hVc, subset_closure (by simp), ?_,
    h.odd_inf_four_centralizer_eq_bot A V a.odd_card hVc⟩
  rw [closure_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · exact a.z_mem_normalizer
  · exact a.normalizer_zpowers_le htN

/-- The full ambient centralizer of the elementary order-27 complement is
exactly the complement. In particular its normalizer acts faithfully modulo it. -/
public theorem OddCentralizerComplement.centralizer_eq_of_elementary_twentySeven
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27) :
    centralizer (A : Set G) = A := by
  let _ := he
  have hodd : Odd (Nat.card (centralizer (A : Set G))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro hd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
      (G := centralizer (A : Set G)) 2 hd
    have htG : orderOf (t : G) = 2 :=
      (orderOf_injective (centralizer (A : Set G)).subtype Subtype.val_injective t).trans ht
    have hAC : A ≤ centralizer ({(t : G)} : Set G) := by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp t.property y hy)
    have hdA := card_dvd_of_le hAC
    rw [hc, h.involution_centralizer_card t htG] at hdA
    norm_num at hdA
  apply le_antisymm ?_ (Subgroup.le_centralizer A)
  intro y hy
  apply (a.mem_iff_odd_orderOf ?_).mpr
  · have ho := hodd.of_dvd_nat (orderOf_dvd_natCard
      (⟨y, hy⟩ : centralizer (A : Set G)))
    rwa [← orderOf_injective (centralizer (A : Set G)).subtype Subtype.val_injective] at ho
  · exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hy x a.x_mem).symm

/-- The kernel of the literal normalizer action is the relative copy of A. -/
public theorem OddCentralizerComplement.normalizer_action_ker_of_elementary_twentySeven
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27) :
    A.normalizerMonoidHom.ker = A.subgroupOf (normalizer (A : Set G)) := by
  rw [normalizerMonoidHom_ker, a.centralizer_eq_of_elementary_twentySeven he hc]

/-- The actual action image has index equal to the index of A in its normalizer. -/
public theorem OddCentralizerComplement.normalizer_card_of_elementary_twentySeven
    [IsSimpleGroup G] {h : Janko1CentralizerData G} {x : G} {A : Subgroup G}
    (a : OddCentralizerComplement h x A)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27) :
    Nat.card (normalizer (A : Set G)) = 27 * Nat.card A.normalizerMonoidHom.range := by
  have hk : Nat.card A.normalizerMonoidHom.ker = 27 := by
    rw [a.normalizer_action_ker_of_elementary_twentySeven he hc,
      Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv, hc]
  calc
    _ = Nat.card A.normalizerMonoidHom.ker * A.normalizerMonoidHom.ker.index :=
      A.normalizerMonoidHom.ker.card_mul_index.symm
    _ = _ := by rw [hk, index_ker]

include h in
/-- Every involution has at most a line of fixed points on an elementary
order-27 subgroup. This uses its actual ambient centralizer of order 120. -/
public theorem elementary_twentySeven_involution_fixed_card_dvd
    [IsSimpleGroup G] (A : Subgroup G) (hc : Nat.card A = 27)
    (t : G) (ht : orderOf t = 2) :
    Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) ∣ 3 := by
  have hA := card_dvd_of_le (show A ⊓ centralizer ({t} : Set G) ≤ A from inf_le_left)
  have hC := card_dvd_of_le
    (show A ⊓ centralizer ({t} : Set G) ≤ centralizer ({t} : Set G) from inf_le_right)
  rw [hc] at hA
  rw [h.involution_centralizer_card t ht] at hC
  exact (by norm_num : Nat.gcd 27 120 = 3) ▸ Nat.dvd_gcd hA hC

end CFSG.Quasithin.Janko1CentralizerData
