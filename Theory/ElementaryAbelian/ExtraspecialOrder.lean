module
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.FieldTheory.Finite.Basic
/-!
# The odd power order of an extraspecial group

Commutation gives a nondegenerate alternating form on the elementary central
quotient. Its even dimension proves |P|=p^(2n+1). In particular, a binary
extraspecial group of order greater than 32 and at most 128 has order 128.
The DGS binary unitary core uses this gap after its upper bound is established.

The pairing proof is reused from the checked private extraspecial_order in
Representation.PrimeFixedPointCentralization.MinimalStructure.CyclicCenter,
with only its group and linear-algebra dependencies. Source: the standard
extraspecial commutator pairing, applied in DGS85 (11.8), p.176.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace IsExtraspecial
private def centralCommutatorHom {P : Type*} [Group P]
    (hc : _root_.commutator P ≤ center P) (x : P) : P →* center P where
  toFun y := ⟨⁅x,y⁆, hc (commutator_mem_commutator (mem_top x) (mem_top y))⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅x,a*b⁆ = ⁅x,a⁆ * ⁅x,b⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,a⁆ a ⁅x,b⁆,
      mem_center_iff.mp (hc (commutator_mem_commutator (mem_top x) (mem_top b))) a]
    simp only [← mul_assoc, mul_inv_cancel_right]
theorem exists_card_eq_prime_odd_power {q : ℕ} [Fact q.Prime]
    {P : Type*} [Group P] [Finite P] [IsExtraspecial q P] :
    ∃ n : ℕ, Nat.card P = q ^ (2 * n + 1) := by
  classical
  let V := P ⧸ center P
  let π := QuotientGroup.mk' (center P)
  let _ : IsElementaryAbelian q V := IsExtraspecial.quotient_elementary_abelian q P
  have hc : _root_.commutator P ≤ center P :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  let e : center P ≃* Multiplicative (ZMod q) := by
    have hcard := IsExtraspecial.center_order_p q P
    exact (zmodCyclicMulEquiv (isCyclic_of_prime_card hcard)).symm.trans
      (ZMod.ringEquivCongr hcard).toAddEquiv.toMultiplicative
  have hkill (x : P) : center P ≤ (centralCommutatorHom hc x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  let pairing : P →* (V →* center P) := {
    toFun x := QuotientGroup.lift (center P) (centralCommutatorHom hc x) (hkill x)
    map_one' := by
      apply MonoidHom.ext
      intro v
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
      apply Subtype.ext
      change ⁅(1 : P), y⁆ = 1
      simp
    map_mul' x y := by
      apply MonoidHom.ext
      intro v
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
      apply Subtype.ext
      change ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (hc (commutator_mem_commutator (mem_top y) (mem_top z))) x]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp
        (hc (commutator_mem_commutator (mem_top y) (mem_top z))) ⁅x, z⁆).symm }
  have hker : center P ≤ pairing.ker := by
    intro x hx
    apply MonoidHom.ext
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    apply Subtype.ext
    change ⁅x,y⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm
  let qp : V →* (V →* center P) := QuotientGroup.lift (center P) pairing hker
  let F : Additive V →+ (Additive V →ₗ[ZMod q] ZMod q) := {
    toFun x := ((e.toMonoidHom.comp (qp x.toMul)).toAdditiveLeft).toZModLinearMap q
    map_zero' := by
      ext y
      change Multiplicative.toAdd (e (qp 1 y.toMul)) = 0
      simp
    map_add' x y := by
      ext z
      change Multiplicative.toAdd (e (qp (x.toMul * y.toMul) z.toMul)) =
        Multiplicative.toAdd (e (qp x.toMul z.toMul)) +
        Multiplicative.toAdd (e (qp y.toMul z.toMul))
      rw [map_mul, MonoidHom.mul_apply, map_mul]
      rfl }
  let B : LinearMap.BilinForm (ZMod q) (Additive V) := F.toZModLinearMap q
  have hB (x y : P) : B (Additive.ofMul (π x)) (Additive.ofMul (π y)) =
      Multiplicative.toAdd (e ⟨⁅x,y⁆,
        hc (commutator_mem_commutator (mem_top x) (mem_top y))⟩) := rfl
  have hzero (x y : P) : B (Additive.ofMul (π x)) (Additive.ofMul (π y)) = 0 ↔
      ⁅x,y⁆ = 1 := by
    rw [hB]
    change e ⟨⁅x,y⁆, _⟩ = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact Subgroup.mk_eq_one (center P)
  have hAlt : B.IsAlt := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hv : v = Additive.ofMul (π x) := congrArg Additive.ofMul hx.symm
    rw [hv, hzero]
    exact commutatorElement_self x
  have hLeft : B.SeparatingLeft := by
    intro v hv
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hvx : v = Additive.ofMul (π x) := congrArg Additive.ofMul hx.symm
    rw [hvx]
    change π x = 1
    apply (QuotientGroup.eq_one_iff (N := center P) x).mpr
    apply mem_center_iff.mpr
    intro y
    have hh := hv (Additive.ofMul (π y))
    rw [hvx, hzero] at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  have hNondeg : B.Nondegenerate :=
    ⟨hLeft, fun v hv => hLeft v (fun w => hAlt.isRefl w v (hv w))⟩
  obtain ⟨n, hn⟩ := AlternatingForm.even_finrank B hAlt hNondeg
  let : Fintype V := Fintype.ofFinite V
  have hV : Nat.card V = q ^ (2 * n) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive V)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card, hn, two_mul] using hh
  refine ⟨n, ?_⟩
  have hh := (center P).card_mul_index
  rw [index_eq_card, IsExtraspecial.center_order_p q P] at hh
  rw [← hh, hV, pow_succ, Nat.mul_comm]


/-- In the next binary interval, extraspecial parity forces order 128. -/
theorem card_eq_128_of_bounds {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hl : 32 < Nat.card P) (hu : Nat.card P ≤ 128) : Nat.card P = 128 := by
  obtain ⟨n,hn⟩ := exists_card_eq_prime_odd_power (q := 2) (P := P)
  have hl' : 5 < 2*n+1 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [hn] using hl
  have hu' : 2*n+1 ≤ 7 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    simpa only [hn] using hu
  have he : n = 3 := by omega
  simpa [he] using hn

end IsExtraspecial
