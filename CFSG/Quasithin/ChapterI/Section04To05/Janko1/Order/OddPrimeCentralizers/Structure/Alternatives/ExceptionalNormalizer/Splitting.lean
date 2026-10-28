module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.Alternatives.ComplementAction
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

/-!
# Lifting the exceptional four-group normalizer

Suppose the normalizer of the order-27 complement has order 324 and its
product with a normalizing four-group is normal in that normalizer.
Normalizer lifting through the odd kernel gives a supplement normalizing
the four-group. The supplement meets the odd kernel in its fixed subgroup,
which is trivial. Consequently it has order twelve; a subgroup of order
three in it completes the required full ambient decomposition.

This is a conditional construction step for Bender (1974), (4.1), printed
p.225. The order and relative-normality premises must still be established
from the action on the elementary order-27 complement. No splitting of a
three-extension is assumed.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

private theorem odd_normal_four_split
    {G : Type*} [Group G] [Finite G]
    (A V : Subgroup G) [A.Normal]
    (hcA : Nat.card A = 27) (hcV : Nat.card V = 4)
    (hn : (A ⊔ V).Normal)
    (hfix : A ⊓ centralizer (V : Set G) = ⊥)
    (hcard : Nat.card G = 324) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ normalizer (V : Set G) ∧
      (⊤ : Subgroup G) = A ⊔ (V ⊔ X) := by
  let q := QuotientGroup.mk' A
  let _ : (A ⊔ V).Normal := hn
  have hVq : (V.map q).Normal := by
    have hmap : ((A ⊔ V).map q).Normal :=
      Subgroup.Normal.map hn q (QuotientGroup.mk'_surjective A)
    have heq : (A ⊔ V).map q = V.map q := by
      rw [Subgroup.map_sup, show A.map q = ⊥ from (Subgroup.map_eq_bot_iff A).mpr (by simp [q]), bot_sup_eq]
    exact heq ▸ hmap
  let _ : (V.map q).Normal := hVq
  let _ : Fact (IsPGroup 2 V) := ⟨IsPGroup.of_card (n := 2) (by simpa using hcV)⟩
  have hmapN : (normalizer (V : Set G)).map q = ⊤ := by
    rw [← normalizer_map_quotient_eq_map_normalizer 2 V A inferInstance
      (by rw [hcA]; decide)]
    exact normalizer_eq_top _
  have hcover : normalizer (V : Set G) ⊔ A = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hmapN
    simpa only [q, QuotientGroup.comap_map_mk', comap_top, sup_comm A] using hh
  have hdis : Disjoint A V := disjoint_of_coprime_natCard (by rw [hcA, hcV]; decide)
  have hdisN : Disjoint A (normalizer (V : Set G)) := by
    rw [disjoint_def]
    intro a ha haN
    have hca : a ∈ centralizer (V : Set G) := by
      intro v hv
      have hAV : a * v * a⁻¹ * v⁻¹ ∈ V :=
        V.mul_mem ((mem_normalizer_iff.mp haN v).mp hv) (V.inv_mem hv)
      have hAA : a * v * a⁻¹ * v⁻¹ ∈ A := by
        rw [mul_assoc a v a⁻¹, mul_assoc a (v * a⁻¹) v⁻¹]
        exact A.mul_mem ha ((inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) v)
      have he : a * v * a⁻¹ * v⁻¹ = 1 := disjoint_def.mp hdis hAA hAV
      exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm
    have : a ∈ A ⊓ centralizer (V : Set G) := ⟨ha, hca⟩
    rwa [hfix, mem_bot] at this
  have hNcard : Nat.card (normalizer (V : Set G)) = 12 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A (normalizer (V : Set G))
      (by rw [normalizer_eq_top A]; exact le_top)
    rw [hdisN.eq_bot, card_bot, one_mul, sup_comm A, hcover, card_top, hcA, hcard] at hh
    omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer (V : Set G)) 3 (by rw [hNcard]; decide)
  have hyG : orderOf (y : G) = 3 :=
    (orderOf_injective (normalizer (V : Set G)).subtype Subtype.val_injective y).trans hy
  let X := zpowers (y : G)
  have hX : Nat.card X = 3 := by rw [Nat.card_zpowers, hyG]
  have hXN : X ≤ normalizer (V : Set G) := zpowers_le.mpr y.property
  have hVX : V ⊔ X = normalizer (V : Set G) := by
    apply eq_of_le_of_card_ge (sup_le V.le_normalizer hXN)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint V X hXN
      (disjoint_of_coprime_natCard (by rw [hcV, hX]; decide)), hcV, hX, hNcard]
  exact ⟨X, hX, hXN, by rw [hVX, sup_comm, hcover]⟩

/-- Lift the normal four-subgroup of the order-12 automizer to the full
ambient normalizer decomposition. Normality here is relative to N_G(A). -/
public theorem exceptionalOddNormalizer_of_order_and_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (A V : Subgroup G)
    (he : IsElementaryAbelian 3 A) (hc : Nat.card A = 27)
    (hVe : IsElementaryAbelian 2 V) (hVc : Nat.card V = 4)
    (hVN : V ≤ normalizer (A : Set G))
    (hn : ((A ⊔ V).subgroupOf (normalizer (A : Set G))).Normal)
    (hcard : Nat.card (normalizer (A : Set G)) = 324) :
    ExceptionalOddNormalizer A := by
  let N := normalizer (A : Set G)
  let AN := A.subgroupOf N
  let VN := V.subgroupOf N
  have hAN : A ≤ N := A.le_normalizer
  have hANcard : Nat.card AN = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hc
  have hVNcard : Nat.card VN = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv).trans hVc
  have hAVN : (AN ⊔ VN).Normal := by
    rw [← subgroupOf_sup hAN hVN]
    exact hn
  have hfix : AN ⊓ centralizer (VN : Set N) = ⊥ := by
    apply bot_unique
    rintro y ⟨hyA, hyC⟩
    have hyG : (y : G) ∈ A ⊓ centralizer (V : Set G) := by
      refine ⟨hyA, ?_⟩
      intro v hv
      exact congrArg Subtype.val (hyC ⟨v, hVN hv⟩ hv)
    have hzero := h.odd_inf_four_centralizer_eq_bot A V (by rw [hc]; decide) hVc
    rw [hzero, mem_bot] at hyG
    exact Subtype.ext hyG
  obtain ⟨X, hXc, hXN, hcover⟩ := odd_normal_four_split AN VN hANcard hVNcard hAVN hfix hcard
  refine ⟨he, hc, V, X.map N.subtype, hVe, hVc, ?_, ?_, ?_⟩
  · rw [card_map_of_injective Subtype.val_injective, hXc]
  · rintro y ⟨u, hu, rfl⟩
    have huN := hXN hu
    rw [← subgroupOf_normalizer_eq hVN] at huN
    exact huN
  · have hh := congrArg (Subgroup.map N.subtype) hcover
    have hAm : AN.map N.subtype = A := map_subgroupOf_eq_of_le hAN
    have hVm : VN.map N.subtype = V := map_subgroupOf_eq_of_le hVN
    simpa only [Subgroup.map_sup, hAm, hVm, ← MonoidHom.range_eq_map,
      range_subtype] using hh

end CFSG.Quasithin.Janko1CentralizerData
