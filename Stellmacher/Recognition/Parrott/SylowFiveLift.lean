module

public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Lifts in a Sylow-five normalizer

For H=C_G(z) and J=O₂(H), every element of H/J has a representative
in the normalizer of the supplied Sylow-five subgroup P. Indeed, the
Sylow-five subgroup of the quotient of order twenty is normal, and the
coprime quotient normalizer theorem lifts its normalizer. Disjointness
of J and P implies N_J(P)=C_J(P), which lies in Z(J).

Consequently, if a quotient element has n-th power one, a representative
can be chosen whose n-th power lies in Z(J). In particular, the fourth
power of a suitable lift of an order-four quotient element centralizes J′.
This statement does not infer the order of a lift from its quotient order.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.674, the choice of x in N_H(P) with x⁴=1 or z.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

/-- Lift a quotient element through a Sylow-five normalizer, so any power
that vanishes in the quotient belongs to the center of the core. -/
public theorem parrott_quotient_exists_lift_pow_mem_core_center
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ (v : H ⧸ J) (n : ℕ), v ^ n = 1 → ∃ y : H,
      QuotientGroup.mk' J y = v ∧ y ^ n ∈ (center J).map J.subtype := by
  intro H J v n hv
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let q := QuotientGroup.mk' J
  obtain ⟨P, hP⟩ := h.five_centralizer
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
  obtain ⟨y, hy, hyv⟩ := hnorm.symm ▸ (mem_top v)
  have hyJ : y ^ n ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (y ^ n) = 1
    rw [map_pow, hyv, hv]
  have hyN : y ^ n ∈ normalizer (P : Set H) := pow_mem hy n
  have hdis : Disjoint J (P : Subgroup H) :=
    IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup P.isPGroup'
  have hyC : y ^ n ∈ centralizer (P : Set H) := by
    intro p hp
    have hcJ : ⁅y ^ n, p⁆ ∈ J :=
      commutator_le_left J (⊤ : Subgroup H)
        (commutator_mem_commutator hyJ (mem_top p))
    have hcP : ⁅y ^ n, p⁆ ∈ (P : Subgroup H) := by
      exact P.mul_mem ((mem_normalizer_iff.mp hyN p).mp hp) (P.inv_mem hp)
    have hone : ⁅y ^ n, p⁆ = 1 := (disjoint_def.mp hdis) hcJ hcP
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  exact ⟨y, hyv, mem_map_of_mem J.subtype (hP hyC : (⟨y ^ n, hyJ⟩ : J) ∈ center J)⟩
end Stellmacher.Recognition
