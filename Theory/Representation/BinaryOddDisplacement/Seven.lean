module

public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.RepEquiv
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# Self-dual binary displacement for commuting cubic and septic actors

The two nontrivial factors of X⁷−1 over the binary field are the reciprocal
cubics X³+X+1 and X³+X²+1. Their kernel spaces are a direct sum complement
to the fixed space of the order-seven actor. Self-duality pairs these kernels:
contragredience replaces the actor by its inverse and transposes its operator,
which preserves nullity.

On either kernel the order-seven actor has no fixed vectors. A commuting
fixed-point-free cubic actor also has no fixed vectors on that kernel.
Fixed-point counting makes its dimension divisible by both three and two.
The two equal kernel dimensions therefore make the displacement divisible by
twelve, and faithfulness makes it positive. This proves the required bound
without a character table or an assumed constituent classification.

Source: the odd-order displacement argument for Aschbacher–Smith H.12.1,
printed p.394. Construction of the commuting actors and the actual self-duality
equivalence belongs to the application.
-/

open Polynomial
namespace Representation.BinaryOddDisplacement
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
private def factorOperator (ρ : Representation (ZMod 2) G V) (x : G) (i : ℕ) :
    Module.End (ZMod 2) V := ρ (x ^ 3) + ρ (x ^ i) + 1
private abbrev factorSpace (ρ : Representation (ZMod 2) G V) (x : G) (i : ℕ) :=
    (factorOperator ρ x i).ker
private lemma factorOperator_commute (ρ : Representation (ZMod 2) G V) (x y : G)
    (i : ℕ) (hxy : Commute x y) : Commute (factorOperator ρ x i) (ρ y) :=
  (((hxy.pow_left 3).map ρ).add_left ((hxy.pow_left i).map ρ)).add_left
    (Commute.one_left _)

private def factorSubrepresentation (ρ : Representation (ZMod 2) G V) (x y : G)
    (i : ℕ) (hxy : Commute x y) : Subrepresentation (ρ.comp (Subgroup.zpowers y).subtype) :=
  ⟨factorSpace ρ x i, by
    intro g v hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have hc := factorOperator_commute ρ x g i (hn ▸ hxy.zpow_right n)
    change factorOperator ρ x i (ρ g v) = 0
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hv, map_zero]⟩

private lemma factorSpace_fixed_eq_zero (ρ : Representation (ZMod 2) G V) (x : G) (i : ℕ)
    (v : V) (hv : v ∈ factorSpace ρ x i) (hfix : ρ x v = v) : v = 0 := by
  have hp (n : ℕ) : ρ (x ^ n) v = v := by
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ, map_mul, Module.End.mul_apply, hfix, ih]
  change (ρ (x ^ 3) v + ρ (x ^ i) v) + v = 0 at hv
  rw [hp, hp] at hv
  have hvv : v + v = 0 := by
    have h := congrArg (fun a : ZMod 2 => a • v) (show (2 : ZMod 2) = 0 by decide)
    simpa only [two_smul, zero_smul] using h
  simpa only [hvv, zero_add] using hv

variable [FiniteDimensional (ZMod 2) V]

set_option backward.isDefEq.respectTransparency false in
private lemma factorSpace_six_dvd (ρ : Representation (ZMod 2) G V) (x z : G)
    (hx : orderOf x = 7) (hz : orderOf z = 3) (hxz : Commute x z)
    (hfix : invariants (ρ.comp (Subgroup.zpowers z).subtype) = ⊥) (i : ℕ) :
    6 ∣ Module.finrank (ZMod 2) (factorSpace ρ x i) := by
  let S := factorSubrepresentation ρ x x i (Commute.refl x)
  let T := factorSubrepresentation ρ x z i hxz
  have hS : S.toRepresentation.invariants = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    apply Subtype.ext
    exact factorSpace_fixed_eq_zero ρ x i v v.property
      (congrArg Subtype.val (hv ⟨x, Subgroup.mem_zpowers x⟩))
  have hT : T.toRepresentation.invariants = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    apply Subtype.ext
    have hv' : v.val ∈ invariants (ρ.comp (Subgroup.zpowers z).subtype) :=
      fun g => congrArg Subtype.val (hv g)
    rwa [hfix] at hv'
  have h3 : 3 ∣ Module.finrank (ZMod 2) (factorSpace ρ x i) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_seven, S, factorSubrepresentation] using
      BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup S.toRepresentation
        (by decide : Nat.Prime 7) (by decide)
        (IsPGroup.of_card (p := 7) (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)) hS
  have h2 : 2 ∣ Module.finrank (ZMod 2) (factorSpace ρ x i) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_three, T, factorSubrepresentation] using
      BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup T.toRepresentation
        (by decide : Nat.Prime 3) (by decide)
        (IsPGroup.of_card (p := 3) (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hz)) hT
  exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3


omit [FiniteDimensional (ZMod 2) V] in
private lemma factorSpace_finrank_equiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (e : ρ ≃ₗ σ) (x : G) (i : ℕ) :
    Module.finrank (ZMod 2) (factorSpace ρ x i) =
      Module.finrank (ZMod 2) (factorSpace σ x i) := by
  have he (v : V) : e (factorOperator ρ x i v) = factorOperator σ x i (e v) := by
    change e.toLinearEquiv (ρ (x ^ 3) v + ρ (x ^ i) v + v) = _
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (e.isIntertwining _ v)
      (e.isIntertwining _ v)) rfl
  have hh : (factorSpace σ x i).comap e.toLinearMap = factorSpace ρ x i := by
    ext v
    change factorOperator σ x i (e v) = 0 ↔ factorOperator ρ x i v = 0
    rw [← he]
    exact e.toLinearEquiv.map_eq_zero_iff
  rw [← hh]
  exact (e.toLinearEquiv.ofSubmodule' (factorSpace σ x i)).finrank_eq

private lemma factorSpace_finrank_dual (ρ : Representation (ZMod 2) G V) (x : G) (i : ℕ) :
    Module.finrank (ZMod 2) (factorSpace ρ.dual x i) =
      Module.finrank (ZMod 2) (factorSpace ρ x⁻¹ i) := by
  have he : factorOperator ρ.dual x i = (factorOperator ρ x⁻¹ i).dualMap := by
    ext f v
    simp [factorOperator, Representation.dual, ← inv_pow]
  change Module.finrank (ZMod 2) (factorOperator ρ.dual x i).ker = _
  rw [he]
  have h1 := (factorOperator ρ x⁻¹ i).finrank_range_add_finrank_ker
  have h2 := (factorOperator ρ x⁻¹ i).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h2
  change Module.finrank (ZMod 2) (factorOperator ρ x⁻¹ i).dualMap.ker =
    Module.finrank (ZMod 2) (factorOperator ρ x⁻¹ i).ker
  omega

omit [FiniteDimensional (ZMod 2) V] in
private lemma factorSpace_inverse (ρ : Representation (ZMod 2) G V) (x : G) :
    factorSpace ρ x⁻¹ 1 = factorSpace ρ x 2 := by
  have he : ρ (x ^ 3) * factorOperator ρ x⁻¹ 1 = factorOperator ρ x 2 := by
    simp only [factorOperator, mul_add, ← map_mul, mul_one, pow_one]
    have h1 : x ^ 3 * (x⁻¹) ^ 3 = 1 := by group
    have h2 : x ^ 3 * x⁻¹ = x ^ 2 := by group
    rw [h1, h2, map_one]
    abel
  have hinj : Function.Injective (ρ (x ^ 3)) := by
    intro v w h
    have hh := congrArg (ρ (x ^ 3)⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh
  ext v
  change factorOperator ρ x⁻¹ 1 v = 0 ↔ factorOperator ρ x 2 v = 0
  rw [← he, Module.End.mul_apply]
  symm
  simpa only [map_zero] using
    (hinj.eq_iff (a := factorOperator ρ x⁻¹ 1 v) (b := 0))

private lemma factorSpace_finrank_selfDual (ρ : Representation (ZMod 2) G V)
    (e : ρ ≃ₗ ρ.dual) (x : G) :
    Module.finrank (ZMod 2) (factorSpace ρ x 1) =
      Module.finrank (ZMod 2) (factorSpace ρ x 2) := by
  rw [factorSpace_finrank_equiv ρ ρ.dual e, factorSpace_finrank_dual,
    factorSpace_inverse]


private lemma fixedCodim_eq_factorSpace_sum (ρ : Representation (ZMod 2) G V)
    (x : G) (hx : x ^ 7 = 1) :
    BinaryOffender.fixedCodim ρ (Subgroup.zpowers x) =
      Module.finrank (ZMod 2) (factorSpace ρ x 1) +
      Module.finrank (ZMod 2) (factorSpace ρ x 2) := by
  let p : (ZMod 2)[X] := X ^ 3 + X + 1
  let q : (ZMod 2)[X] := X ^ 3 + X ^ 2 + 1
  let r : (ZMod 2)[X] := X - 1
  have hpq : IsCoprime p q := by
    refine ⟨X, X + 1, ?_⟩
    dsimp [p, q]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hrp : IsCoprime r p := by
    refine ⟨X ^ 2 + X, 1, ?_⟩
    dsimp [r, p]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hrq : IsCoprime r q := by
    refine ⟨X ^ 2, 1, ?_⟩
    dsimp [r, q]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hrpq : IsCoprime r (p * q) := hrp.mul_right hrq
  have hprod : r * (p * q) = X ^ 7 - 1 := by
    dsimp [r, p, q]
    ring_nf
    simp [CharTwo.ofNat_eq_mod, CharTwo.neg_eq]
  have hp : (aeval (ρ x) p).ker = factorSpace ρ x 1 := by
    congr 1
    simp [p, factorOperator]
  have hq : (aeval (ρ x) q).ker = factorSpace ρ x 2 := by
    congr 1
    simp [q, factorOperator]
  have hr : (aeval (ρ x) r).ker = BinaryOffender.fixedSpace ρ (Subgroup.zpowers x) := by
    ext v
    rw [BinaryOffender.mem_fixedSpace_zpowers_iff]
    simp [r, LinearMap.mem_ker, sub_eq_zero]
  have hz : aeval (ρ x) (r * (p * q)) = 0 := by
    rw [hprod]
    rw [map_sub, map_pow, aeval_X, map_one, ← map_pow, hx, map_one, sub_self]
  have hcompl : IsCompl (aeval (ρ x) r).ker (aeval (ρ x) (p * q)).ker := by
    refine ⟨disjoint_ker_aeval_of_isCoprime _ hrpq, codisjoint_iff.mpr ?_⟩
    rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hrpq, hz, LinearMap.ker_zero]
  have hsum := sup_ker_aeval_eq_ker_aeval_mul_of_coprime (ρ x) hpq
  rw [hp, hq] at hsum
  have hdis := disjoint_ker_aeval_of_isCoprime (ρ x) hpq
  rw [hp, hq] at hdis
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (factorSpace ρ x 1) (factorSpace ρ x 2)
  rw [hdis.eq_bot, finrank_bot, add_zero, hsum] at hd
  have hc := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hr] at hc
  have hf := BinaryOffender.fixedCodim_add_finrank ρ (Subgroup.zpowers x)
  omega



end Representation.BinaryOddDisplacement

namespace Representation.BinaryOffender
open Subgroup BinaryOddDisplacement
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Self-duality and a commuting fixed-point-free cubic actor make septic
binary displacement divisible by twelve. Faithfulness is unnecessary. -/
public theorem twelve_dvd_fixedCodim_of_selfDual_three_seven
    (ρ : Representation (ZMod 2) G V) (e : ρ ≃ₗ ρ.dual)
    (z x : G) (hz : orderOf z = 3) (hx : orderOf x = 7)
    (hzx : Commute z x) (hfix : invariants (ρ.comp (zpowers z).subtype) = ⊥) :
    12 ∣ fixedCodim ρ (zpowers x) := by
  have hd := fixedCodim_eq_factorSpace_sum ρ x (hx ▸ pow_orderOf_eq_one x)
  have he := factorSpace_finrank_selfDual ρ e x
  have hdiv := factorSpace_six_dvd ρ x z hx hz hzx.symm hfix 1
  omega

variable [Finite G]

/-- A faithful self-dual binary module with a fixed-point-free cubic actor
moves at least twelve dimensions under a commuting order-seven actor. -/
public theorem twelve_le_fixedCodim_of_selfDual_three_seven
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (e : ρ ≃ₗ ρ.dual) (z x : G) (hz : orderOf z = 3) (hx : orderOf x = 7)
    (hzx : Commute z x) (hfix : invariants (ρ.comp (zpowers z).subtype) = ⊥) :
    12 ≤ fixedCodim ρ (zpowers x) := by
  have hdiv := twelve_dvd_fixedCodim_of_selfDual_three_seven ρ e z x hz hx hzx hfix
  have hpos := prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 7) (by decide) x hx
  rw [BinaryPrimeDegree.orderOf_two_mod_seven] at hpos
  omega

/-- In dimension twelve the order-seven actor has full displacement. -/
public theorem fixedCodim_eq_twelve_of_selfDual_three_seven
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (e : ρ ≃ₗ ρ.dual) (z x : G) (hz : orderOf z = 3) (hx : orderOf x = 7)
    (hzx : Commute z x) (hfix : invariants (ρ.comp (zpowers z).subtype) = ⊥)
    (hdim : Module.finrank (ZMod 2) V = 12) :
    fixedCodim ρ (zpowers x) = 12 := by
  have hlo := twelve_le_fixedCodim_of_selfDual_three_seven ρ hρ e z x hz hx hzx hfix
  have h := fixedCodim_add_finrank ρ (zpowers x)
  omega
end Representation.BinaryOffender
