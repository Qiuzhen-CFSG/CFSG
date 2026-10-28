module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Definitions
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.Sylow
public import Mathlib.GroupTheory.SchurZassenhaus
public import Theory.GroupAction.ThreeOnElementaryEight
public import Theory.SpecificGroups.Frobenius21.Recognition

/-!
# The marked normalizer in Janko's uniqueness argument

Using the earlier order calculation `|N_G(S)| = 168`, Schur–Zassenhaus
constructs an order-21 complement H to the actual Sylow subgroup S. Every
cubic element of H acts nontrivially on the self-centralizing elementary
eight S, so its fixed subgroup has order two.

H cannot be abelian: an element of order seven commuting with its cubic
subgroup would fix that involution, whereas every involution centralizer
has order 120. The recognition of the nonabelian group of order 21 then
supplies marked generators y,u with `uyu⁻¹ = y²`. This constructs the
`NormalizerFrame` used by the remaining involution and matrix arguments.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, the configuration
preceding (6.2); Z. Janko, J. Algebra 3 (1966), 147–186. The input 168 is
the earlier normalizer calculation also used in Bender (1974), §4. No
involution w or normalized representation is asserted to exist here.
The final export supplies the proved normalizer order from the original
local hypotheses, leaving no numerical premise in the frame construction.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- Split the actual Sylow normalizer, retaining its literal subgroup inclusions. -/
public theorem exists_complement
    (hN : Nat.card (normalizer (h.sylow : Set G)) = 168) :
    ∃ H : Subgroup G, Nat.card H = 21 ∧
      H ≤ normalizer (h.sylow : Set G) ∧
      Disjoint H (h.sylow : Subgroup G) ∧
      H ⊔ (h.sylow : Subgroup G) = normalizer (h.sylow : Set G) := by
  let S := (h.sylow : Subgroup G)
  let N := normalizer (S : Set G)
  let T := S.subgroupOf N
  have hT : Nat.card T = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv).trans h.sylow_card
  have hi : T.index = 21 := by
    have he := T.card_mul_index
    change Nat.card T * T.index = Nat.card (normalizer (h.sylow : Set G)) at he
    rw [hT, hN] at he
    omega
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card T) T.index by rw [hT, hi]; decide)
  let H := K.map N.subtype
  have hH : Nat.card H = 21 := by
    rw [card_map_of_injective N.subtype_injective, ← hK.symm.index_eq_card, hi]
  refine ⟨H, hH, map_subtype_le _, ?_, ?_⟩
  · exact disjoint_of_coprime_natCard (by rw [hH, h.sylow_card]; decide)
  · have he := congrArg (fun A : Subgroup N => A.map N.subtype) hK.symm.sup_eq_top
    change (K ⊔ S.subgroupOf N).map N.subtype = (⊤ : Subgroup N).map N.subtype at he
    rw [Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
      range_subtype] at he
    have hSN : S ≤ N := S.le_normalizer
    rw [inf_eq_left.mpr hSN] at he
    exact he

/-- Every cubic normalizer element fixes exactly one involution in the Sylow subgroup. -/
public theorem cubic_fixed_involution (u : G)
    (hun : u ∈ normalizer (h.sylow : Set G)) (hu : orderOf u = 3) :
    ∃ x : G, x ∈ (h.sylow : Subgroup G) ∧ orderOf x = 2 ∧
      (h.sylow : Subgroup G) ⊓ centralizer (zpowers u : Set G) = zpowers x := by
  let S := (h.sylow : Subgroup G)
  let U := zpowers u
  have hUn : U ≤ normalizer (S : Set G) := zpowers_le.mpr hun
  let f : U →* MulAut S := S.normalizerMonoidHom.comp (inclusion hUn)
  let : MulDistribMulAction U S := MulDistribMulAction.compHom S f
  let C := FixedPoints.subgroup U S
  have hU : Nat.card U = 3 := (Nat.card_zpowers u).trans hu
  have hnon : commutatorAction U S ≠ ⊥ := by
    intro he
    have hc : u ∈ centralizer (S : Set G) := by
      rw [mem_centralizer_iff]
      intro s hs
      have hd : (⟨s, hs⟩ : S)⁻¹ * ((⟨u, mem_zpowers u⟩ : U) • (⟨s, hs⟩ : S)) ∈
          commutatorAction U S := by
        rw [commutatorAction_eq_closure]
        exact subset_closure ⟨⟨u, mem_zpowers u⟩, ⟨s, hs⟩, rfl⟩
      rw [he, mem_bot] at hd
      have hfix := inv_mul_eq_one.mp hd
      have heq : s = u * s * u⁻¹ := congrArg Subtype.val hfix
      exact (mul_inv_eq_iff_eq_mul.mp heq.symm).symm
    change u ∈ centralizer (h.sylow : Set G) at hc
    rw [h.sylow_centralizer_eq] at hc
    have hu2 : u ^ 2 = 1 := congrArg Subtype.val (h.sylow_square ⟨u, hc⟩)
    have hd := orderOf_dvd_of_pow_eq_one hu2
    rw [hu] at hd
    norm_num at hd
  let := h.sylow_elementaryAbelian
  have hC : Nat.card C = 2 :=
    (card_three_action_on_eight_fixed_commutator_card hU h.sylow_card hnon).1
  let D := S ⊓ centralizer (U : Set G)
  have hCD : C.map S.subtype = D := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.property, mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have heq : a * (t : G) * a⁻¹ = t := congrArg Subtype.val (ht ⟨a, ha⟩)
      exact mul_inv_eq_iff_eq_mul.mp heq
    · rintro ⟨hs, hc⟩
      refine ⟨⟨s, hs⟩, ?_, rfl⟩
      intro a
      apply Subtype.ext
      change (a : G) * s * (a : G)⁻¹ = s
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc a a.property)
  have hD : Nat.card D = 2 := by
    rw [← hCD, card_map_of_injective S.subtype_injective, hC]
  obtain ⟨x, hx, _⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hD
  have hx1 : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : orderOf (x : G) = 2 :=
    orderOf_eq_prime_iff.mpr
      ⟨congrArg Subtype.val (h.sylow_square ⟨x, x.property.1⟩), hx1⟩
  refine ⟨x, x.property.1, hx2, ?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr x.property) ?_).symm
  rw [Nat.card_zpowers, hx2, hD]

/-- An order-21 subgroup of the Sylow normalizer is nonabelian. -/
public theorem complement_noncommutative [IsSimpleGroup G]
    (H : Subgroup G) (hH : Nat.card H = 21)
    (hHn : H ≤ normalizer (h.sylow : Set G)) :
    ¬ ∀ a b : H, a * b = b * a := by
  classical
  intro hab
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (by rw [hH]; decide)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (by rw [hH]; decide)
  have huG : orderOf (u : G) = 3 := (H.orderOf_coe u).trans hu
  have hyG : orderOf (y : G) = 7 := (H.orderOf_coe y).trans hy
  obtain ⟨x, hxS, hx2, hfix⟩ := cubic_fixed_involution h u (hHn u.property) huG
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx2
  have hxC : x ∈ centralizer (zpowers (u : G) : Set G) :=
    ((hfix ▸ mem_zpowers x) : x ∈ (h.sylow : Subgroup G) ⊓
      centralizer (zpowers (u : G) : Set G)).2
  have hux : Commute (u : G) x :=
    mem_centralizer_iff.mp hxC u (mem_zpowers _)
  have huy : Commute (u : G) (y : G) := congrArg Subtype.val (hab u y)
  let t := (y : G) * x * (y : G)⁻¹
  have htC : t ∈ centralizer (zpowers (u : G) : Set G) := by
    have hc : Commute (u : G) t := (huy.mul_right hux).mul_right huy.inv_right
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact (hc.zpow_left n).eq
  have htS : t ∈ (h.sylow : Subgroup G) :=
    (mem_normalizer_iff.mp (hHn y.property) x).mp hxS
  have ht : t ∈ zpowers x := hfix ▸ (show t ∈
    (h.sylow : Subgroup G) ⊓ centralizer (zpowers (u : G) : Set G) from ⟨htS, htC⟩)
  have ht1 : t ≠ 1 := by
    intro he
    exact hx1 ((MulAut.conj (y : G)).injective (he.trans (map_one _).symm))
  rw [mem_zpowers_iff_mem_range_orderOf, hx2] at ht
  obtain ⟨n, hn, hn'⟩ := Finset.mem_image.mp ht
  have hn2 := Finset.mem_range.mp hn
  have htx : t = x := by
    interval_cases n
    · exact (ht1 (by simpa using hn'.symm)).elim
    · simpa using hn'.symm
  have hyC : (y : G) ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp htx)
  have hd := orderOf_dvd_natCard (⟨y, hyC⟩ : centralizer ({x} : Set G))
  rw [Subgroup.orderOf_mk, hyG, h.involution_centralizer_card x hx2] at hd
  norm_num at hd

private def a21 : Frobenius21.Model := SemidirectProduct.inl (Multiplicative.ofAdd 1)
private def b21 : Frobenius21.Model := SemidirectProduct.inr (Multiplicative.ofAdd 1)

private theorem pair21 :
    a21 ^ 7 = 1 ∧ a21 ≠ 1 ∧ b21 ^ 3 = 1 ∧ b21 ≠ 1 ∧
      b21 * a21 * b21⁻¹ = a21 ^ 2 ∧
      ∀ m : Frobenius21.Model, ∃ i : Fin 7, ∃ j : Fin 3,
        m = a21 ^ i.val * b21 ^ j.val := by decide +kernel

/-- Construct all of the source normalizer configuration from its order.
The normalizer-order theorem remains an explicit earlier source input. -/
public theorem exists_normalizerFrame [IsSimpleGroup G]
    (hN : Nat.card (normalizer (h.sylow : Set G)) = 168) :
    Nonempty (NormalizerFrame h) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨H, hH, hHn, hHS, hsup⟩ := exists_complement h hN
  obtain ⟨e⟩ := Frobenius21.nonempty_mulEquiv_of_card_eq hH
    (complement_noncommutative h H hH hHn)
  let f : Frobenius21.Model →* G := H.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp e.symm.injective
  obtain ⟨ha7, ha1, hb3, hb1, hact, hwords⟩ := pair21
  have hy : orderOf (f a21) = 7 := by
    rw [orderOf_injective f hf]
    exact orderOf_eq_prime_iff.mpr ⟨ha7, ha1⟩
  have hu : orderOf (f b21) = 3 := by
    rw [orderOf_injective f hf]
    exact orderOf_eq_prime_iff.mpr ⟨hb3, hb1⟩
  have hyH : f a21 ∈ H := (e.symm a21).property
  have huH : f b21 ∈ H := (e.symm b21).property
  obtain ⟨x, hxS, hx2, hfix⟩ := cubic_fixed_involution h (f b21) (hHn huH) hu
  refine ⟨⟨H, f a21, f b21, x, hH, hHn, hHS, hsup, hyH, huH, hy, hu,
    ?_, ?_, hxS, hx2, hfix⟩⟩
  · apply le_antisymm (sup_le (zpowers_le.mpr hyH) (zpowers_le.mpr huH))
    intro g hg
    obtain ⟨i, j, hm⟩ := hwords (e ⟨g, hg⟩)
    have hgm : f (e ⟨g, hg⟩) = g := congrArg Subtype.val (e.symm_apply_apply _)
    rw [← hgm, hm, map_mul, map_pow, map_pow]
    exact Subgroup.mul_mem_sup (pow_mem (mem_zpowers _) _) (pow_mem (mem_zpowers _) _)
  · simpa only [map_mul, map_inv, map_pow] using congrArg f hact

/-- The original finite simple group hypotheses supply the marked `7:3`
normalizer configuration, with no additional normalizer-order premise. -/
public theorem exists_normalizerFrame_of_source [IsSimpleGroup G] :
    Nonempty (NormalizerFrame h) :=
  exists_normalizerFrame h h.sylow_normalizer_card

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
