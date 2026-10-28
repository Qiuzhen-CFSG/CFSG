module
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupAction.InvertedFifteenOnSixteen
public import Theory.GroupTheory.Involution.Basic
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.NonsplitFour
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# Involution-generated normalizers of the smallest binary prime actions

A normal three-group acting faithfully on a binary plane, together with any
involution, generates the full actor. A normal five-group acting faithfully on
four binary dimensions has the same property when involutions generate the
actor. In both cases the involution commutator is the marked prime subgroup.

For five, the centralizer has order dividing fifteen. Every involution inverts
the prime subgroup, so products of two involutions lie in that centralizer.
The impossibility of inverting an order-fifteen automorphism on sixteen binary
vectors forces each such product into the marked five-group. For three, the
order of GL₂(2) bounds the actor, and a kernel-checked calculation over the
sixteen binary two-by-two matrices excludes a centralizing involution.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
D.2.23–24, printed pp.189–190. These endpoints replace the full semilinear
normalizer calculation by the precise involution-generation conclusion used
there. No self-centralizing hypothesis is imposed on the prime subgroup.
-/

noncomputable section
open Subgroup
open scoped commutatorElement
local notation "IsInvolution" => BenderSuzuki.PFAppendixIII.IsInvolution
namespace SmallBinaryPrimeNormalizer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem involution_not_mem_odd (C : Subgroup G) (hC : Odd (Nat.card C))
    (t : G) (ht : IsInvolution t) : t ∉ C := by
  intro hm
  have ho : orderOf (⟨t, hm⟩ : C) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime ht.2 ht.1
  exact hC.not_two_dvd_nat (ho ▸ orderOf_dvd_natCard (⟨t, hm⟩ : C))

private theorem prime_inverted {p : ℕ} [Fact p.Prime]
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = p)
    (hC : Odd (Nat.card (centralizer (D : Set G))))
    (t : G) (ht : IsInvolution t) :
    ∀ x ∈ D, t * x * t⁻¹ = x⁻¹ := by
  let φ : MulAut D := MulAut.conjNormal t
  have hf : MonoidHom.FixedPointFree φ := by
    intro x hx
    by_contra hne
    have hφ : φ = 1 := by
      ext y
      obtain ⟨n, hy⟩ := mem_zpowers_iff.mp
        (show y ∈ zpowers x from mem_zpowers_of_prime_card hD hne)
      rw [← hy]
      simp only [map_zpow, hx, MulAut.one_apply]
    apply involution_not_mem_odd _ hC t ht
    rw [← MulAut.conjNormal_ker_eq_centralizer D]
    exact hφ
  have hi : Function.Involutive φ := by
    intro x
    have he := congrArg (fun a : MulAut D => a x)
      (show φ * φ = 1 by
        change MulAut.conjNormal t * MulAut.conjNormal t = 1
        rw [← map_mul, ← pow_two, ht.2, map_one])
    exact he
  intro x hx
  exact congrArg Subtype.val (congrFun (hf.coe_eq_inv_of_involutive hi) ⟨x, hx⟩)

private theorem commutator_prime_eq {p : ℕ} [Fact p.Prime]
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = p)
    (t : G) (htC : t ∉ centralizer (D : Set G)) : ⁅D, zpowers t⁆ = D := by
  have hle := commutator_le_left D (zpowers t)
  have hd : Nat.card (⁅D, zpowers t⁆ : Subgroup G) ∣ p := hD ▸ card_dvd_of_le hle
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
  · have hb := (eq_bot_iff_card ⁅D, zpowers t⁆).mpr h
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hb
    exact (htC (hb (mem_zpowers t))).elim
  · exact eq_of_le_of_card_ge hle (by rw [h, hD])

private theorem mem_five_of_centralizing_fifth_power
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 5)
    (hC : Nat.card (centralizer (D : Set G)) ≤ 15)
    (x : G) (hxC : x ∈ centralizer (D : Set G)) (hx : x ^ 5 = 1) : x ∈ D := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  have hDC : D ≤ centralizer (D : Set G) := D.le_centralizer
  have hJ : IsPGroup 5 (D ⊔ zpowers x : Subgroup G) :=
    (IsPGroup.of_card (n := 1) (by simpa using hD)).to_sup_of_normal_left
      (by
        intro y
        refine ⟨1, Subtype.ext ?_⟩
        obtain ⟨n, hn⟩ := y.property
        change x ^ n = (y : G) at hn
        change (y : G) ^ (5 ^ 1) = 1
        rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm n,
          zpow_mul, zpow_natCast, hx, one_zpow])
  have hbound : Nat.card (D ⊔ zpowers x : Subgroup G) ≤ 15 :=
    (card_le_of_le (sup_le hDC (zpowers_le.mpr hxC))).trans hC
  obtain ⟨n, hn⟩ := hJ.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hnle
    have hp : 25 ≤ 5 ^ n := by
      exact Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 2 ≤ n)
    omega
  have he : D ⊔ zpowers x = D := (eq_of_le_of_card_ge le_sup_left (by
    rw [hD, hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 5) hnle)).symm
  exact he ▸ mem_sup_right (mem_zpowers x)

variable {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
  [MulDistribMulAction G V] [FaithfulSMul G V]

omit [Finite G] in
private theorem no_inverted_fifteen (hV : Nat.card V = 16)
    (a t : G) (ha : orderOf a = 15) (ht : t ^ 2 = 1) :
    t * a * t⁻¹ ≠ a⁻¹ := by
  let φ := MulDistribMulAction.toMulAut G V
  have hf : Function.Injective φ := by
    intro a b he
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    exact congrArg (fun f : MulAut V => f v) he
  apply fun h => MulAut.not_inverts_order_fifteen_on_sixteen hV (φ a) (φ t)
    (by rw [orderOf_injective φ hf, ha])
    (by rw [← map_pow, ht, map_one]) (by simpa only [map_mul, map_inv] using congrArg φ h)

public theorem involution_mul_mem_five
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 5) (hV : Nat.card V = 16)
    (s t : G) (hs : IsInvolution s) (ht : IsInvolution t) : s * t ∈ D := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := centralizer (D : Set G)
  have hCdvd : Nat.card C ∣ 15 := card_centralizer_five_dvd_fifteen (V := V) D hD hV
  have hCodd : Odd (Nat.card C) := (by decide : Odd 15).of_dvd_nat hCdvd
  have hi := prime_inverted D hD hCodd t ht
  have hsC : s * t ∈ C := by
    rw [mem_centralizer_iff]
    intro a ha
    have he : (s * t) * a * (s * t)⁻¹ = a := by
      rw [mul_inv_rev]
      calc
        s * t * a * (t⁻¹ * s⁻¹) = s * (t * a * t⁻¹) * s⁻¹ := by group
        _ = s * a⁻¹ * s⁻¹ := by rw [hi a ha]
        _ = a := by rw [prime_inverted D hD hCodd s hs a⁻¹ (D.inv_mem ha), inv_inv]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hprod : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
    rw [mul_inv_rev, hs.inv_eq_self, ht.inv_eq_self]
    rw [mul_assoc, mul_assoc, ← pow_two, ht.2, mul_one]
  have hdiv : orderOf (s * t) ∣ 15 := by
    have hd := orderOf_dvd_natCard (⟨s * t, hsC⟩ : C)
    rw [← orderOf_coe] at hd
    exact hd.trans hCdvd
  have hcases : orderOf (s * t) = 1 ∨ orderOf (s * t) = 3 ∨
      orderOf (s * t) = 5 ∨ orderOf (s * t) = 15 := by
    have hm := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 15 ≠ 0)⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hcases with h | h | h | h
  · exact (orderOf_eq_one_iff.mp h) ▸ D.one_mem
  · obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 (by rw [hD])
    have hac : Commute (a : G) (s * t) := mem_centralizer_iff.mp hsC a a.property
    have hao : orderOf ((a : G) * (s * t)) = 15 := by
      rw [hac.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [orderOf_coe, ha, h]; decide),
        orderOf_coe, ha, h]
    apply (no_inverted_fifteen (V := V) hV ((a : G) * (s * t)) t hao ht.2).elim
    calc
      t * ((a : G) * (s * t)) * t⁻¹ =
          (t * (a : G) * t⁻¹) * (t * (s * t) * t⁻¹) := by group
      _ = (a : G)⁻¹ * (s * t)⁻¹ := by rw [hi a a.property, hprod]
      _ = ((a : G) * (s * t))⁻¹ := hac.mul_inv.symm
  · exact mem_five_of_centralizing_fifth_power D hD (Nat.le_of_dvd (by decide) hCdvd)
      (s * t) hsC (h ▸ pow_orderOf_eq_one (s * t))
  · exact (no_inverted_fifteen (V := V) hV (s * t) t h ht.2 hprod).elim

/-- Involutions generate exactly the dihedral extension of the normal five-group. -/
public theorem five_generation
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 5) (hV : Nat.card V = 16)
    (hgen : closure {s : G | IsInvolution s} = ⊤)
    (t : G) (ht : IsInvolution t) : D ⊔ zpowers t = ⊤ ∧ ⁅D, zpowers t⁆ = D := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    intro s hs
    have hm : s * t ∈ D ⊔ zpowers t :=
      mem_sup_left (involution_mul_mem_five (V := V) D hD hV s t hs ht)
    have he : s * t * t⁻¹ = s := by group
    exact he ▸ (D ⊔ zpowers t).mul_mem hm
      ((D ⊔ zpowers t).inv_mem (mem_sup_right (mem_zpowers t)))
  · apply commutator_prime_eq D hD t
    apply involution_not_mem_odd _ _ t ht
    exact (by decide : Odd 15).of_dvd_nat
      (card_centralizer_five_dvd_fifteen (V := V) D hD hV)

end SmallBinaryPrimeNormalizer

namespace Representation.SmallBinaryPrimeNormalizer
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem matrix_two_three_centralizer :
    ∀ a b : Matrix (Fin 2) (Fin 2) (ZMod 2),
    a ^ 3 = 1 → a ≠ 1 → b ^ 2 = 1 → a * b = b * a → b = 1 := by
  decide +kernel

/-- The order-three action in its least binary degree has no centralizing involution. -/
public theorem involution_not_centralizes_three
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (D : Subgroup G) (hD : Nat.card D = 3)
    (t : G) (ht : IsInvolution t) : t ∉ centralizer (D : Set G) := by
  intro hc
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hD])
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let m := LinearMap.toMatrixAlgEquiv b
  have han : ρ (a : G) ≠ 1 := by
    intro he
    have h : (a : G) = 1 := hf (he.trans ρ.map_one.symm)
    have ha1 : a = 1 := Subtype.ext h
    simp [ha1] at ha
  have hmat := matrix_two_three_centralizer (m (ρ a)) (m (ρ t))
    (by rw [← map_pow, ← map_pow, show (a : G) ^ 3 = 1 from
      congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a), map_one, map_one])
    (fun he => han (m.injective (he.trans m.map_one.symm)))
    (by rw [← map_pow, ← map_pow, ht.2, map_one, map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
      (mem_centralizer_iff.mp hc) a a.property])
  exact ht.1 (hf ((m.injective (hmat.trans m.map_one.symm)).trans ρ.map_one.symm))

/-- A normal three-group on a binary plane and any involution generate the actor. -/
public theorem three_generation
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 3)
    (t : G) (ht : IsInvolution t) : D ⊔ zpowers t = ⊤ ∧ ⁅D, zpowers t⁆ = D := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card G ≤ 6 := by
    have hd := card_dvd_card_GL_of_injective ρ hf
    rw [hdim, Matrix.card_GL_field] at hd
    norm_num [Fin.prod_univ_two] at hd
    exact Nat.le_of_dvd (by decide) hd
  have htD : t ∉ D := _root_.SmallBinaryPrimeNormalizer.involution_not_mem_odd D
    (by rw [hD]; decide) t ht
  have hjoin : Nat.card (D ⊔ zpowers t : Subgroup G) = 6 := by
    rw [card_sup_zpowers_of_normalizing_involution D t ht.2 htD
      (by rw [D.normalizer_eq_top]; trivial), hD]
  constructor
  · exact eq_top_of_card_eq _ (le_antisymm (Nat.card_le_card_of_injective
      (D ⊔ zpowers t).subtype (D ⊔ zpowers t).subtype_injective)
      (by rw [hjoin]; exact hcard))
  · exact _root_.SmallBinaryPrimeNormalizer.commutator_prime_eq D hD t
      (involution_not_centralizes_three ρ hf hdim D hD t ht)

/-- The faithful binary representation wrapper for the order-five endpoint. -/
public theorem five_generation
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (D : Subgroup G) [D.Normal] (hD : Nat.card D = 5)
    (hgen : closure {s : G | IsInvolution s} = ⊤)
    (t : G) (ht : IsInvolution t) : D ⊔ zpowers t = ⊤ ∧ ⁅D, zpowers t⁆ = D := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := W)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite W := (Module.finite_iff_finite (R := ZMod 2)).mp inferInstance
  apply _root_.SmallBinaryPrimeNormalizer.five_generation (V := Multiplicative W) D hD _ hgen t ht
  change Nat.card W = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  rfl

end Representation.SmallBinaryPrimeNormalizer
