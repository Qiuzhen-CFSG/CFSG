module

public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolutionConjugacy

/-!
# The two involution representatives in a Sylow-five normalizer

Put H=C_G(z) and J=O₂(H). For a supplied Sylow-five subgroup P satisfying
C_J(P) ≤ Z(J), every involution of N_H(P) outside J is H-conjugate to an
arbitrary supplied such involution y or to yz.

The unique Sylow-five subgroup of H/J is normal, so coprime normalizer
lifting makes N_H(P) surject onto H/J. Involutions in the faithful C₅⋊C₄
quotient are conjugate. Lift a conjugator inside N_H(P); the difference
between the resulting elements belongs to N_H(P) ∩ J. Disjointness of J
and P makes this difference centralize P, hence lie in Z(J)=⟨z⟩.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.674, final paragraph. The normalizer surjectivity argument is
also used in `SylowFiveLift`; no order of an arbitrary lift is assumed.
-/

open Subgroup

open scoped commutatorElement
namespace Stellmacher.Recognition

private theorem normalizer_surjects
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z)
    (P : Sylow 5 (centralizer ({z} : Set G))) :
    (normalizer (P : Set (centralizer ({z} : Set G)))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) = ⊤ := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let q := QuotientGroup.mk' J
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective J)
  have hQcard : Nat.card (H ⧸ J) = 20 := by
    obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
    calc
      _ = Nat.card (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4)) φ) := Nat.card_congr e.toEquiv
      _ = 20 := by rw [SemidirectProduct.card]; norm_num
  have hQc : Nat.card Q = 5 := by
    rw [Q.card_eq_multiplicity, hQcard]
    decide +kernel
  have hQi : Q.index = 4 := by
    have hh := Q.index_mul_card
    rw [hQc, hQcard] at hh
    omega
  have hcount : Nat.card (Sylow 5 (H ⧸ J)) = 1 := by
    have hdiv := Q.card_dvd_index
    rw [hQi] at hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < 4) hdiv
    have hmod := card_sylow_modEq_one 5 (H ⧸ J)
    unfold Nat.ModEq at hmod
    omega
  let : Subsingleton (Sylow 5 (H ⧸ J)) :=
    (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (Q : Subgroup (H ⧸ J)).Normal := Q.normal_of_subsingleton
  let : Fact (IsPGroup 5 (P : Subgroup H)) := ⟨P.isPGroup'⟩
  have hnorm : (normalizer (P : Set H)).map q = ⊤ := by
    change (normalizer ((P : Subgroup H) : Set H)).map (QuotientGroup.mk' J) = ⊤
    rw [← normalizer_map_quotient_eq_map_normalizer 5 (P : Subgroup H) J
      inferInstance (by rw [h.core_card]; decide)]
    change normalizer (Q : Set (H ⧸ J)) = ⊤
    exact normalizer_eq_top (H := (Q : Subgroup (H ⧸ J)))
  exact hnorm

/-- Every outer involution in the supplied Sylow-five normalizer is conjugate
in H to the supplied y or to yz. The centralizer hypothesis is imposed on the
supplied Sylow subgroup, and y remains arbitrary. -/
public theorem parrott_five_normalizer_involution_classes
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ (P : Sylow 5 H), (centralizer (P : Set H)).subgroupOf J ≤ center J →
    ∀ y u : H, y ∈ normalizer (P : Set H) → y ∉ J → orderOf y = 2 →
      u ∈ normalizer (P : Set H) → u ∉ J → orderOf u = 2 →
      ∃ c : H, c * u * c⁻¹ = y ∨
        (c : G) * (u : G) * (c : G)⁻¹ = (y : G) * z := by
  classical
  intro H J P hP y u hyN hyJ hy huN huJ hu
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let q := QuotientGroup.mk' J
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder (v : H) (hvJ : v ∉ J) (hv : orderOf v = 2) : orderOf (q v) = 2 := by
    apply orderOf_eq_prime
    · have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
      rw [← map_pow, hv2, map_one]
    · intro he
      exact hvJ ((QuotientGroup.eq_one_iff _).mp he)
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  obtain ⟨a, ha⟩ := faithful_five_four_involutions_conjugate φ hφ (e (q y)) (e (q u))
    ((e.orderOf_eq _).trans (horder y hyJ hy))
    ((e.orderOf_eq _).trans (horder u huJ hu))
  have ha' : e.symm a * q u * (e.symm a)⁻¹ = q y := by
    apply e.injective
    simpa using ha
  have hsurj := normalizer_surjects z h P
  obtain ⟨c, hcN, hc⟩ := hsurj.symm ▸ (mem_top (e.symm a))
  let v := c * u * c⁻¹
  have hvN : v ∈ normalizer (P : Set H) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem hcN huN) ((normalizer _).inv_mem hcN)
  have hvq : q v = q y := by
    change q (c * u * c⁻¹) = q y
    rw [map_mul, map_mul, map_inv, hc]
    exact ha'
  -- Equal quotient images leave a difference in N_H(P) ∩ J.
  let d := y⁻¹ * v
  have hdJ : d ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (y⁻¹ * v) = 1
    rw [map_mul, map_inv, hvq, inv_mul_cancel]
  have hdN : d ∈ normalizer (P : Set H) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem hyN) hvN
  have hdis : Disjoint J (P : Subgroup H) :=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup P.isPGroup'
  -- Normalizing elements of J centralize P by coprime disjointness.
  have hdC : d ∈ centralizer (P : Set H) := by
    intro p hp
    have hcJ : ⁅d, p⁆ ∈ J :=
      commutator_le_left J (⊤ : Subgroup H)
        (commutator_mem_commutator hdJ (mem_top p))
    have hcP : ⁅d, p⁆ ∈ (P : Subgroup H) :=
      P.mul_mem ((mem_normalizer_iff.mp hdN p).mp hp) (P.inv_mem hp)
    have hone : ⁅d, p⁆ = 1 := (disjoint_def.mp hdis) hcJ hcP
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  -- The fixed-centralizer hypothesis puts this difference in ⟨z⟩.
  have hdZ : (d : G) ∈ zpowers z := by
    rw [← (parrott_centralizer_structure z h).1]
    exact mem_map_of_mem (H.subtype.comp J.subtype)
      (hP hdC : (⟨d, hdJ⟩ : J) ∈ center J)
  have hd_cases : (d : G) = 1 ∨ (d : G) = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hdZ
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hdZ
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using heq.symm)
    · exact Or.inr (by simpa using heq.symm)
  refine ⟨c, ?_⟩
  rcases hd_cases with hd | hd
  · left
    have hdH : d = 1 := Subtype.ext hd
    exact (inv_mul_eq_one.mp hdH).symm
  · right
    change (y : G)⁻¹ * ((c : G) * (u : G) * (c : G)⁻¹) = z at hd
    exact inv_mul_eq_iff_eq_mul.mp hd
end Stellmacher.Recognition
