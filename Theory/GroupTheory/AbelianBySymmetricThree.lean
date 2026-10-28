module

public import Theory.GroupTheory.OddInvolutionNormalizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.Perm

/-!
# Odd subgroups of an abelian-by-S₃ group

Let A be a normal odd abelian subgroup with quotient S₃. An odd subgroup H
normalized by an involution t has C_H(t) inside A. Its fixed-point index
therefore divides three times [A : C_A(t)]. If N(H) ≤ H⟨t⟩, those two
fixed-point indices cannot be equal.

For the last assertion, pass to H A and then factor out H ∩ A. The image
of H has order three and is self-normalizing. Sylow's fixed-coset congruence
makes its index prime to three, contradicting |H| dividing |A|. This proves
the Sylow-three obstruction without a Hall decomposition or residual notation.

`constraints_in_normalizer` applies the calculation to the literal quotient
N(F)/(F.subgroupOf N(F)); F is normal only in its normalizer.

Source: GLS, Volume 4, Chapter 2, Lemma 17.4, especially (17G) and the
following Sylow argument (`refs/KGroup/GLS4/Chapter2.tex`). The concrete
unitary torus construction is a separate prerequisite.
-/

public section

open Subgroup

namespace Subgroup.AbelianBySymmetricThree
variable {G : Type*} [Group G] [Finite G]

private theorem prime_not_dvd_index_of_self_normalizing
    {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (hcard : Nat.card H = p) (hN : normalizer H = H) : ¬ p ∣ H.index := by
  have hm := Sylow.card_quotient_normalizer_modEq_card_quotient
    (p := p) (n := 1) (H := H) (by simpa using hcard)
  change (H.subgroupOf (normalizer H)).index ≡ H.index [MOD p] at hm
  rw [hN, subgroupOf_self, index_top] at hm
  intro hd
  have : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp (hm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  exact (Fact.out : p.Prime).not_dvd_one this

/-- A self-normalizing subgroup supplemented by a normal abelian subgroup
has index prime to the prime order of its image modulo that supplement. -/
theorem prime_not_dvd_index_of_abelian_supplement
    {p : ℕ} [Fact p.Prime] (A H : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hgen : H ⊔ A = ⊤) (hrel : A.relIndex H = p)
    (hN : normalizer H = H) : ¬ p ∣ H.index := by
  let B := H ⊓ A
  have hAN : A ≤ normalizer B :=
    ((le_centralizer A).trans (centralizer_le inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hHN : H ≤ normalizer B :=
    (le_inf H.le_normalizer (show H ≤ normalizer A from le_normalizer_of_normal)).trans
      inf_normalizer_le_normalizer_inf
  have hBN : B.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le hHN hAN))
  let f := QuotientGroup.mk' B
  let P := H.map f
  have hker : f.ker ≤ H := by
    rw [QuotientGroup.ker_mk']
    exact inf_le_left
  have hcomap : P.comap f = H := comap_map_eq_self hker
  have hPN : normalizer P = P := by
    apply comap_injective (QuotientGroup.mk'_surjective B)
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective B), hcomap, hN]
  have hcard : Nat.card P = p := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    simpa only [B, inf_relIndex_left] using hrel
  have hi : P.index = H.index := by
    rw [← index_comap_of_surjective P (QuotientGroup.mk'_surjective B), hcomap]
  rw [← hi]
  exact prime_not_dvd_index_of_self_normalizing P hcard hPN

omit [Finite G] in
private theorem card_mul_relIndex (A H : Subgroup G) (h : A ≤ H) :
    Nat.card A * A.relIndex H = Nat.card H := by
  simpa only [relIndex_bot_left] using
    (relIndex_mul_relIndex (⊥ : Subgroup G) A H bot_le h)

/-- Normalizer control by an involution prevents the odd subgroup order
from dividing the order of a normal odd abelian subgroup of index six. -/
theorem not_card_dvd_of_abelian_normal_index_six
    (A H : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (hAi : A.index = 6)
    (hHodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2)
    (htN : t ∈ normalizer H) (hN : normalizer H ≤ H ⊔ zpowers t) :
    ¬ Nat.card H ∣ Nat.card A := by
  have htH : t ∉ H := by
    intro h
    have hd := _root_.orderOf_dvd_natCard (⟨t, h⟩ : H)
    rw [Subgroup.orderOf_mk, ht] at hd
    exact hHodd.not_two_dvd_nat hd
  have hdouble := card_sup_zpowers_of_normalizing_involution H t
    (ht ▸ pow_orderOf_eq_one t) htH htN
  have hnot : ¬ H ≤ A := by
    intro hHA
    have heq : H = A := eq_odd_abelian_overgroup_of_normalizer_le H A hHA hAodd ht htN hN
    subst H
    have htop : (⊤ : Subgroup G) ≤ A ⊔ zpowers t := by
      simpa only [A.normalizer_eq_top] using hN
    have hc : Nat.card G = 2 * Nat.card A := by
      simpa only [top_unique htop, Nat.card_congr (Subgroup.topEquiv.toEquiv)] using hdouble
    have ha := A.card_mul_index
    rw [hAi, hc] at ha
    have : 0 < Nat.card A := Nat.card_pos
    omega
  have hr : A.relIndex H = 3 := by
    have hd : A.relIndex H ∣ 6 := hAi ▸ relIndex_dvd_index_of_normal A H
    have ho := Odd.of_dvd_nat hHodd (A.relIndex_dvd_card H)
    have hn : A.relIndex H ≠ 1 := fun he => hnot (relIndex_eq_one.mp he)
    have hd3 : A.relIndex H ∣ 3 := ho.coprime_two_right.dvd_of_dvd_mul_left hd
    exact ((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left hn
  let M := H ⊔ A
  have hHM : H ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have hMcard : Nat.card M = Nat.card A * 3 := by
    rw [← card_mul_relIndex A M hAM]
    rw [show A.relIndex M = A.relIndex H from relIndex_sup_right H A, hr]
  have hModd : Odd (Nat.card M) := by rw [hMcard]; exact hAodd.mul (by decide)
  have hNM : normalizer H ⊓ M = H := by
    have hHK : H ≤ normalizer H ⊓ M := le_inf H.le_normalizer hHM
    have ho := Odd.of_dvd_nat hModd (card_dvd_of_le (inf_le_right : normalizer H ⊓ M ≤ M))
    have hd : Nat.card (normalizer H ⊓ M : Subgroup G) ∣ 2 * Nat.card H := by
      rw [← hdouble]
      exact card_dvd_of_le (inf_le_left.trans hN)
    exact (eq_of_le_of_card_ge hHK (Nat.le_of_dvd Nat.card_pos
      (ho.coprime_two_right.dvd_of_dvd_mul_left hd))).symm
  let A' := A.subgroupOf M
  let H' := H.subgroupOf M
  have hN' : normalizer H' = H' := by
    rw [← subgroupOf_normalizer_eq hHM]
    change (normalizer H).subgroupOf M = H.subgroupOf M
    rw [← inf_subgroupOf_right, hNM]
  have hgen : H' ⊔ A' = ⊤ := by
    rw [← subgroupOf_sup hHM hAM]
    exact subgroupOf_self M
  have hr' : A'.relIndex H' = 3 := by
    rw [relIndex_subgroupOf hHM, hr]
  have hprime := prime_not_dvd_index_of_abelian_supplement A' H' hgen hr' hN'
  intro hd
  obtain ⟨k, hk⟩ := hd
  have hc := card_mul_relIndex H M hHM
  rw [hMcard, hk, mul_assoc] at hc
  have hi : H.relIndex M = k * 3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hc
  exact hprime (show 3 ∣ H.relIndex M by rw [hi]; exact dvd_mul_left 3 k)
end Subgroup.AbelianBySymmetricThree

namespace Subgroup.AbelianBySymmetricThree
variable {G : Type*} [Group G] [Finite G]

private theorem perm_three_involution_commuting_square : ∀ a b : Equiv.Perm (Fin 3),
    b ≠ 1 → b ^ 2 = 1 → Commute a b → a ^ 2 = 1 := by
  change ∀ a b : Equiv.Perm (Fin 3), b ≠ 1 → b ^ 2 = 1 → a * b = b * a → a ^ 2 = 1
  decide

omit [Finite G] in
/-- An odd subgroup centralizing an involution has trivial image in S₃
when the homomorphism has odd kernel. -/
theorem odd_centralizer_le_kernel
    (f : G →* Equiv.Perm (Fin 3)) (hkerodd : Odd (Nat.card f.ker))
    (H : Subgroup G) (hHodd : Odd (Nat.card H))
    (t : G) (ht : orderOf t = 2) :
    H ⊓ centralizer ({t} : Set G) ≤ f.ker := by
  have htker : t ∉ f.ker := by
    intro h
    have hd := _root_.orderOf_dvd_natCard (⟨t, h⟩ : f.ker)
    rw [Subgroup.orderOf_mk, ht] at hd
    exact hkerodd.not_two_dvd_nat hd
  have htne : f t ≠ 1 := htker
  have ht2 : (f t) ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hmapodd : Odd (Nat.card (H.map f)) :=
    Odd.of_dvd_nat hHodd (card_map_dvd H f)
  intro x hx
  have hc : Commute (f x) (f t) := by
    apply Commute.map
    exact (mem_centralizer_singleton_iff.mp hx.2)
  have hsq := perm_three_involution_commuting_square (f x) (f t) htne ht2 hc
  let y : H.map f := ⟨f x, mem_map_of_mem f hx.1⟩
  have hy : y ^ 2 = 1 := Subtype.ext hsq
  exact congrArg Subtype.val
    (hmapodd.coprime_two_right.pow_left_bijective.injective (hy.trans (one_pow 2).symm))

omit [Finite G] in
/-- The fixed-point index on an odd subgroup divides three times that
on the normal abelian kernel of an S₃ quotient. -/
theorem centralizer_relIndex_dvd_of_s3_quotient
    (A H : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (e : G ⧸ A ≃* Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2) :
    (centralizer ({t} : Set G)).relIndex H ∣
      3 * (centralizer ({t} : Set G)).relIndex A := by
  let C := centralizer ({t} : Set G)
  have hCnormal : (C.subgroupOf A).Normal := by
    infer_instance
  have hin : (C.subgroupOf A).relIndex ((H ⊓ A).subgroupOf A) ∣
      (C.subgroupOf A).index := relIndex_dvd_index_of_normal _ _
  rw [relIndex_subgroupOf (show H ⊓ A ≤ A from inf_le_right)] at hin
  have hthree : A.relIndex H ∣ 3 := by
    have hindex : A.index = 6 := by
      change Nat.card (G ⧸ A) = 6
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hd := relIndex_dvd_index_of_normal A H
    rw [hindex] at hd
    exact (Odd.of_dvd_nat hHodd (A.relIndex_dvd_card H)).coprime_two_right.dvd_of_dvd_mul_left hd
  let f := e.toMonoidHom.comp (QuotientGroup.mk' A)
  have hker : f.ker = A := by
    ext x
    change e (QuotientGroup.mk' A x) = 1 ↔ x ∈ A
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hle : H ⊓ C ≤ A := by
    rw [← hker]
    exact odd_centralizer_le_kernel f (hker ▸ hAodd) H hHodd t ht
  have heq : (C ⊓ A).relIndex H = C.relIndex H := by
    rw [← inf_relIndex_left H (C ⊓ A), ← inf_relIndex_left H C,
      ← inf_assoc, inf_eq_left.mpr hle]
  change C.relIndex H ∣ 3 * C.relIndex A
  rw [← heq, ← relIndex_inf_mul_relIndex, Nat.mul_comm 3]
  rw [inf_comm H A] at hin
  exact Nat.mul_dvd_mul hin hthree

/-- The two fixed-point indices are distinct under involution normalizer control. -/
theorem centralizer_relIndex_ne_of_s3_quotient
    (A H : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hAodd : Odd (Nat.card A)) (e : G ⧸ A ≃* Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2)
    (htN : t ∈ normalizer H) (hN : normalizer H ≤ H ⊔ zpowers t) :
    (centralizer ({t} : Set G)).relIndex H ≠
      (centralizer ({t} : Set G)).relIndex A := by
  let C := centralizer ({t} : Set G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' A)
  have hker : f.ker = A := by
    ext x
    change e (QuotientGroup.mk' A x) = 1 ↔ x ∈ A
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hle : H ⊓ C ≤ A ⊓ C := by
    refine le_inf ?_ inf_le_right
    rw [← hker]
    exact odd_centralizer_le_kernel f (hker ▸ hAodd) H hHodd t ht
  have hindex : A.index = 6 := by
    change Nat.card (G ⧸ A) = 6
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  intro heq
  apply not_card_dvd_of_abelian_normal_index_six A H hAodd hindex hHodd t ht htN hN
  have hHC := card_mul_relIndex (H ⊓ C) H inf_le_left
  have hAC := card_mul_relIndex (A ⊓ C) A inf_le_left
  rw [inf_relIndex_left, heq] at hHC
  rw [inf_relIndex_left] at hAC
  rw [← hHC, ← hAC]
  exact Nat.mul_dvd_mul (card_dvd_of_le hle) (dvd_refl _)

end Subgroup.AbelianBySymmetricThree

namespace Subgroup.AbelianBySymmetricThree
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer, divisibility and exclusion conclusions inside the actual
normalizer of F. No ambient normality of F is assumed. -/
theorem constraints_in_normalizer
    (F H : Subgroup G) [IsMulCommutative F]
    (hFodd : Odd (Nat.card F))
    (e : normalizer F ⧸ F.subgroupOf (normalizer F) ≃* Equiv.Perm (Fin 3))
    (hHodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2)
    (htN : t ∈ normalizer H) (hN : normalizer H ≤ H ⊔ zpowers t)
    (hinside : H ⊔ zpowers t ≤ normalizer F) :
    H ⊓ centralizer ({t} : Set G) ≤ F ∧
      (centralizer ({t} : Set G)).relIndex H ∣
        3 * (centralizer ({t} : Set G)).relIndex F ∧
      (centralizer ({t} : Set G)).relIndex H ≠
        (centralizer ({t} : Set G)).relIndex F := by
  let M : Subgroup G := normalizer F
  let A := F.subgroupOf M
  let B := H.subgroupOf M
  have hHM : H ≤ M := le_sup_left.trans hinside
  have htM : t ∈ M := hinside ((le_sup_right : zpowers t ≤ H ⊔ zpowers t) (mem_zpowers t))
  let u : M := ⟨t, htM⟩
  have hu : orderOf u = 2 := by simpa only [u, Subgroup.orderOf_mk] using ht
  have hAodd : Odd (Nat.card A) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe F.le_normalizer).toEquiv]
  have hBodd : Odd (Nat.card B) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv]
  have huN : u ∈ normalizer B := by
    rw [← subgroupOf_normalizer_eq hHM]
    exact htN
  have hNB : normalizer B ≤ B ⊔ zpowers u := by
    rw [← subgroupOf_normalizer_eq hHM]
    have hh : (normalizer H).subgroupOf M ≤ (H ⊔ zpowers t).subgroupOf M :=
      subgroupOf_mono M hN
    rw [subgroupOf_sup hHM (zpowers_le.mpr htM)] at hh
    have hz : (zpowers t).subgroupOf M = zpowers u := by
      ext x
      simp only [Subgroup.mem_zpowers_iff, Subgroup.mem_subgroupOf,
        SubgroupClass.coe_zpow, Subtype.ext_iff, u]
    simpa only [hz] using hh
  have hC : centralizer ({u} : Set M) = (centralizer ({t} : Set G)).subgroupOf M := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf, Subtype.ext_iff,
      Subgroup.coe_mul, u]
  have hindicesH : (centralizer ({u} : Set M)).relIndex B =
      (centralizer ({t} : Set G)).relIndex H := by
    rw [hC, relIndex_subgroupOf hHM]
  have hindicesF : (centralizer ({u} : Set M)).relIndex A =
      (centralizer ({t} : Set G)).relIndex F := by
    rw [hC, relIndex_subgroupOf F.le_normalizer]
  refine ⟨?_, ?_, ?_⟩
  · let f := e.toMonoidHom.comp (QuotientGroup.mk' A)
    have hker : f.ker = A := by simp [f]
    have hc := odd_centralizer_le_kernel f (hker ▸ hAodd) B hBodd u hu
    rw [hker, hC] at hc
    intro x hx
    exact hc (show (⟨x, hHM hx.1⟩ : M) ∈ B ⊓
      (centralizer ({t} : Set G)).subgroupOf M from hx)
  · rw [← hindicesH, ← hindicesF]
    exact centralizer_relIndex_dvd_of_s3_quotient A B hAodd e hBodd u hu
  · rw [← hindicesH, ← hindicesF]
    exact centralizer_relIndex_ne_of_s3_quotient A B hAodd e hBodd u hu huN hNB

end Subgroup.AbelianBySymmetricThree
