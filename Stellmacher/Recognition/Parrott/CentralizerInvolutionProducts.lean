module

public import Stellmacher.Recognition.Parrott.OuterFourEighthPower
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Products of involutions in Parrott's first centralizer

Every product of two square-one elements in H = C_G(z) has eighth or
tenth power one. In the quotient C₅ ⋊ C₄ its square or fifth power is
trivial: nonidentity involutions have the same right coordinate. The
square branch uses the fourth-power bound for J = O₂(H). In the fifth-power
branch, a nontrivial fourth power generates a Sylow five subgroup. Sylow
conjugacy and the original fixed-centralizer hypothesis put the commuting
fifth power in Z(J), which has order two.

This uses the actual core and its centralizers, rather than just divisibility
by the order of H. It supplies the first-centralizer branch of Parrott's
braid argument without assumptions about the chosen generator witnesses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 1, printed p.672, and §6, printed p.684, Verification of VI(i).
-/

open Subgroup
namespace Stellmacher.Recognition

private theorem model_involution_products
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (a b : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (a * b) ^ 2 = 1 ∨ (a * b) ^ 5 = 1 := by
  by_cases ha1 : a = 1
  · exact Or.inl (by simpa only [ha1, one_mul] using hb)
  by_cases hb1 : b = 1
  · exact Or.inl (by simpa only [hb1, mul_one] using ha)
  have hr (x : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
      (hx : x ^ 2 = 1) (hx1 : x ≠ 1) : orderOf x.right = 2 := by
    apply orderOf_eq_prime
    · exact congrArg SemidirectProduct.right hx
    · intro he
      have hxleft : x = SemidirectProduct.inl x.left := by ext <;> simp [he]
      have hl2 : x.left ^ 2 = 1 := by
        apply SemidirectProduct.inl_injective (φ := φ)
        simpa only [map_pow, map_one, ← hxleft] using hx
      have hl5 : x.left ^ 5 = 1 := by
        have hh := pow_card_eq_one' (x := x.left)
        norm_num at hh
        exact hh
      have hl : x.left = 1 := by
        have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hl2)
          (orderOf_dvd_of_pow_eq_one hl5)
        norm_num at hd
        exact hd
      apply hx1
      rw [hxleft, hl, map_one]
  have he : a.right = b.right := IsCyclic.eq_of_orderOf_eq_two (hr a ha ha1) (hr b hb hb1)
  have habright : (a * b).right = 1 := by
    rw [SemidirectProduct.mul_right, he, ← pow_two]
    exact (hr b hb hb1) ▸ pow_orderOf_eq_one b.right
  have hab : a * b = SemidirectProduct.inl (a * b).left := by ext <;> simp [habright]
  right
  rw [hab, ← map_pow]
  have hl5 : (a * b).left ^ 5 = 1 := by
    have hh := pow_card_eq_one' (x := (a * b).left)
    norm_num at hh
    exact hh
  rw [hl5, map_one]

private theorem core_square_of_commutes_five
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (a b : centralizer ({z} : Set G))
    (ha : a ∈ pCore 2 (centralizer ({z} : Set G)))
    (hb : orderOf b = 5) (hab : Commute a b) : a ^ 2 = 1 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, hP⟩ := h.five_centralizer
  have hp : IsPGroup 5 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card Q = 5 := by
    rw [Q.card_eq_multiplicity, (h.card_and_solvable z).1]
    decide +kernel
  have hQeq : zpowers b = (Q : Subgroup H) :=
    eq_of_le_of_card_ge hQ (by rw [Nat.card_zpowers, hb, hQcard])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  let c := MulAut.conj g
  have hmap : (zpowers b).map c.toMonoidHom = (P : Subgroup H) := by
    rw [hQeq, ← hg]
    rfl
  have haJ : c a ∈ J := (inferInstance : J.Normal).conj_mem a ha g
  have haC : c a ∈ centralizer (P : Set H) := by
    change c a ∈ centralizer ((P : Subgroup H) : Set H)
    rw [← hmap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg c (hab.zpow_right m).symm.eq
  have haZ : (⟨c a, haJ⟩ : J) ∈ center J := hP haC
  have hc : Nat.card (center J) = 2 := by
    have hh := card_map_of_injective (K := center J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)
    rw [(parrott_centralizer_structure z h).1, Nat.card_zpowers, h.involution] at hh
    exact hh.symm
  have hp2 : (⟨⟨c a, haJ⟩, haZ⟩ : center J) ^ 2 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  apply c.injective
  rw [map_pow, map_one]
  exact congrArg (fun x : center J => ((x : J) : H)) hp2

/-- Products of square-one elements in the actual first centralizer have
eighth or tenth power one. -/
public theorem parrott_centralizer_involution_product_powers
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (a b : centralizer ({z} : Set G)) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (a * b) ^ 8 = 1 ∨ (a * b) ^ 10 = 1 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  have hqa : (e (q a)) ^ 2 = 1 := by rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hqb : (e (q b)) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hb, map_one, map_one]
  rcases model_involution_products φ (e (q a)) (e (q b)) hqa hqb with h2 | h5
  · have habJ : (a * b) ^ 2 ∈ J := by
      apply (QuotientGroup.eq_one_iff (N := J) _).mp
      change q ((a * b) ^ _) = 1
      apply e.injective
      simpa only [map_pow, map_mul, map_one] using h2
    have hh := congrArg J.subtype (parrott_core_fourth_power_eq_one z h ⟨(a * b) ^ 2, habJ⟩)
    change ((a * b) ^ 2) ^ 4 = 1 at hh
    exact Or.inl (by simpa only [← pow_mul] using hh)
  · have habJ : (a * b) ^ 5 ∈ J := by
      apply (QuotientGroup.eq_one_iff (N := J) _).mp
      change q ((a * b) ^ _) = 1
      apply e.injective
      simpa only [map_pow, map_mul, map_one] using h5
    have h20 : (a * b) ^ 20 = 1 := by
      have hh := congrArg J.subtype (parrott_core_fourth_power_eq_one z h ⟨(a * b) ^ 5, habJ⟩)
      change ((a * b) ^ 5) ^ 4 = 1 at hh
      simpa only [← pow_mul] using hh
    by_cases h4 : (a * b) ^ 4 = 1
    · left
      calc (a * b) ^ 8 = ((a * b) ^ 4) ^ 2 := by rw [← pow_mul]
           _ = 1 := by rw [h4, one_pow]
    · have ho5 : orderOf ((a * b) ^ 4) = 5 := orderOf_eq_prime
        (by simpa only [← pow_mul] using h20) h4
      have hh := core_square_of_commutes_five z h ((a * b) ^ 5) ((a * b) ^ 4)
        habJ ho5 (Commute.pow_pow_self _ _ _)
      exact Or.inr (by simpa only [← pow_mul] using hh)
end Stellmacher.Recognition
