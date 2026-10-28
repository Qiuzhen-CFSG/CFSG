module
public import Theory.GroupTheory.Involution.OddRotation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Invariant odd Sylow selection through a prime-index normal subgroup

An inverter modulo a normal kernel remains outside the two-core after
factoring a smaller normal p-subgroup: in the common quotient, an inverted
odd-order element cannot have its square in the two-core. Baer–Suzuki then
finds an inverted odd-prime rotation. When the quotient Sylow has order p
and the group has only the primes 2 and p, its inverse image is the required
invariant Sylow, containing the original normal subgroup.

Source: the common normalizer-quotient argument in Aschbacher–Smith,
12.2.22, printed p.803. The chapter application retains the literal maps.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- An element inverting an odd subgroup modulo a normal kernel cannot lie
in the two-core modulo a smaller normal subgroup. -/
theorem not_mem_twoCore_quotient_of_inverts_modulo
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (P B J : Subgroup G) [B.Normal] [J.Normal]
    (hP : IsPGroup p P) (hBP : B < P) (hJP : J ⊓ P ≤ B)
    (t : G) (hi : ∀ x ∈ P, t * x * t⁻¹ * x ∈ J) :
    QuotientGroup.mk' B t ∉ pCore 2 (G ⧸ B) := by
  let C := B ⊔ J
  let q := QuotientGroup.mk' C
  let f : G ⧸ B →* G ⧸ C := QuotientGroup.map B C (MonoidHom.id G) le_sup_left
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    exact ⟨QuotientGroup.mk' B x, rfl⟩
  have hcore : (pCore 2 (G ⧸ B)).map f ≤ pCore 2 (G ⧸ C) :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  have hdis : Disjoint (P.map q) (pCore 2 (G ⧸ C)) :=
    IsPGroup.disjoint_of_ne p 2 (by intro he; exact ho.not_two_dvd_nat (by rw [he]))
      _ _ (hP.map q) pCore_isPGroup
  intro ht
  have htq : q t ∈ pCore 2 (G ⧸ C) := hcore (mem_map_of_mem f ht)
  have hPC : P ≤ C := by
    intro x hx
    have hix : q t * q x * (q t)⁻¹ = (q x)⁻¹ := by
      have hh := (QuotientGroup.eq_one_iff _).mpr (mem_sup_right (hi x hx) : _ ∈ C)
      change q (t * x * t⁻¹ * x) = 1 at hh
      simpa only [map_mul, map_inv, mul_eq_one_iff_eq_inv] using hh
    have hcomm : ⁅q t, q x⁆ ∈ pCore 2 (G ⧸ C) := by
      have hh := (pCore 2 (G ⧸ C)).mul_mem htq
        ((inferInstance : (pCore 2 (G ⧸ C)).Normal).conj_mem
          (q t)⁻¹ ((pCore 2 (G ⧸ C)).inv_mem htq) (q x))
      simpa only [commutatorElement_def, mul_assoc] using hh
    have hs : (q x)⁻¹ * (q x)⁻¹ = 1 := by
      exact disjoint_def.mp hdis
        ((P.map q).mul_mem ((P.map q).inv_mem (mem_map_of_mem q hx))
          ((P.map q).inv_mem (mem_map_of_mem q hx)))
        (by simpa only [commutatorElement_def, hix] using hcomm)
    have hx2 : q x ^ 2 = 1 := by
      rw [← mul_inv_rev, inv_eq_one] at hs
      simpa only [pow_two] using hs
    have hodd := hP.orderOf_coprime ho.coprime_two_right (⟨x, hx⟩ : P)
    rw [← Subgroup.orderOf_coe] at hodd
    have hqodd : Odd (orderOf (q x)) :=
      (Nat.coprime_two_right.mp hodd).of_dvd_nat (orderOf_map_dvd q x)
    apply (QuotientGroup.eq_one_iff x).mp
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hqodd.coprime_two_right
      dvd_rfl (orderOf_dvd_of_pow_eq_one hx2))
  apply hBP.not_ge
  intro x hx
  obtain ⟨b, hb, j, hj, he⟩ := mem_sup_of_normal_left.mp (hPC hx)
  have hjP : j ∈ P := by
    have hh := P.mul_mem (P.inv_mem (hBP.le hb)) hx
    rwa [← he, inv_mul_cancel_left] at hh
  rw [← he]
  exact B.mul_mem hb (hJP ⟨hj, hjP⟩)

/-- Baer–Suzuki in an index-p normal quotient selects an invariant Sylow
containing the prescribed normal p-subgroup. -/
theorem exists_invariant_sylow_of_prime_relative_index
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (B : Subgroup G) [B.Normal]
    (hBP : B ≤ (P : Subgroup G)) (hidx : B.relIndex (P : Subgroup G) = p)
    (hprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = 2 ∨ r = p)
    (t : G) (ht : t ^ 2 = 1)
    (hmove : QuotientGroup.mk' B t ∉ pCore 2 (G ⧸ B)) :
    ∃ R : Sylow p G, B ≤ (R : Subgroup G) ∧
      t ∈ normalizer (R : Set G) := by
  let q := QuotientGroup.mk' B
  have hti : BenderSuzuki.PFAppendixIII.IsInvolution (q t) :=
    ⟨fun he => hmove (he ▸ (pCore 2 (G ⧸ B)).one_mem), by rw [← map_pow, ht, map_one]⟩
  obtain ⟨r, hr, hr2, a, ha, hi⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime (q t) hti hmove
  have hrp : r = p := (hprimes r hr ((ha ▸ orderOf_dvd_natCard a).trans
    B.index_dvd_card)).resolve_left hr2
  rw [hrp] at ha
  have hi' : q t * a * (q t)⁻¹ = a⁻¹ := by
    simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem, hti.inv_eq_self] using hi
  have hna : q t ∈ normalizer (zpowers a : Set (G ⧸ B)) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (q t * a * (q t)⁻¹) = zpowers a
    rw [hi', zpowers_inv]
  let Pbar := P.mapSurjective (QuotientGroup.mk'_surjective B)
  have hc : Nat.card (Pbar : Subgroup (G ⧸ B)) = p := by
    change Nat.card ((P : Subgroup G).map q) = p
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    exact hidx
  let Rbar : Sylow p (G ⧸ B) := Sylow.ofCard (zpowers a) (by
    rw [Nat.card_zpowers, ha, ← Pbar.card_eq_multiplicity, hc])
  have hk : IsPGroup p q.ker := by
    rw [QuotientGroup.ker_mk']
    exact P.isPGroup'.to_le hBP
  let R : Sylow p G := Rbar.comapOfKerIsPGroup q hk (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective B)]; exact le_top)
  refine ⟨R, ?_, ?_⟩
  · intro x hx
    change q x ∈ zpowers a
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact one_mem _
  · exact (zpowers a).le_normalizer_comap q hna

end Theory.GroupTheory
