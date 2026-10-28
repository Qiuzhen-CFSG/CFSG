module
public import Theory.GroupTheory.CentralExtensionInvariantPairing
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Scalar norms on a central derived group

Suppose a group maps onto an additive vector space with central kernel,
and the nonzero scalars lift to automorphisms of the group. Over a finite
field of order greater than four, every invariant biadditive pairing vanishes.
Indeed, moving a nonzero scalar between the arguments replaces it by its
inverse; comparison at c and 1+c forces vanishing for a suitable scalar c.

Average the central commutator pairing over the scalar group. Its norm
therefore vanishes on the derived group, so every fixed derived element
is annihilated by the order of the scalar group. No dimension restriction
or assertion of field-bilinearity is used.

The application is the defining-prime multiplier exclusion for PSU₃(p²)
in `Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeSquare`.
Source for that application: Aschbacher–Smith I.1.3–4, PDF pp.418–419;
GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

open Subgroup
namespace CentralExtension.ScalarNorm
open scoped commutatorElement IsMulCommutative

private theorem exists_scalar (K : Type*) [Field K] [Finite K]
    (hK : 4 < Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ 1 + c ≠ 0 ∧ (1 + c)⁻¹ ≠ 1 + c⁻¹ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hn (n : ℕ) (hn : n ≤ 3) (hpos : 0 < n) : ¬ a ^ n = 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha, Nat.card_units] at hd
    have := Nat.le_of_dvd hpos hd
    omega
  have hc1 : 1 + (a : K) ≠ 0 := by
    intro h
    apply hn 2 (by decide) (by decide)
    have he : (a : K) = -1 := eq_neg_of_add_eq_zero_right h
    apply Units.ext
    simp [he]
  refine ⟨a, a.ne_zero, hc1, ?_⟩
  intro h
  apply hn 3 (by decide) (by decide)
  have he : (a : K) ^ 2 + a + 1 = 0 := by
    field_simp [hc1] at h
    linear_combination -h
  apply Units.ext
  change (a : K) ^ 3 = 1
  linear_combination ((a : K) - 1) * he

private theorem invariant_pairing_eq_one
    {K V C : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [CommGroup C]
    (hK : 4 < Nat.card K)
    (b : Multiplicative V →* (Multiplicative V →* C))
    (hi : ∀ (t : Kˣ) x y,
      b (.ofAdd ((t : K) • x.toAdd)) (.ofAdd ((t : K) • y.toAdd)) = b x y) : b = 1 := by
  obtain ⟨c, hc, hc1, hne⟩ := exists_scalar K hK
  let B (x y : V) : C := b (.ofAdd x) (.ofAdd y)
  have hl (x y z : V) : B (x+y) z = B x z * B y z := by
    exact congrArg (fun f : Multiplicative V →* C => f (.ofAdd z))
      (b.map_mul (.ofAdd x) (.ofAdd y))
  have hr (x y z : V) : B x (y+z) = B x y * B x z :=
    (b (.ofAdd x)).map_mul (.ofAdd y) (.ofAdd z)
  have hs (s : K) (hs : s ≠ 0) (v w : V) : B (s • v) w = B v (s⁻¹ • w) := by
    have hh := hi (Units.mk0 s hs) (.ofAdd v) (.ofAdd (s⁻¹ • w))
    change B (s • v) (s • (s⁻¹ • w)) = B v (s⁻¹ • w) at hh
    simpa only [smul_smul, mul_inv_cancel₀ hs, one_smul] using hh
  have hz (v : V) : B v 0 = 1 := (b (.ofAdd v)).map_one
  have hneg (v z : V) : B v (-z) = (B v z)⁻¹ := (b (.ofAdd v)).map_inv (.ofAdd z)
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  change B x.toAdd y.toAdd = 1
  have he (w : V) : B x.toAdd ((1+c)⁻¹ • w) = B x.toAdd ((1+c⁻¹) • w) := by
    rw [← hs (1+c) hc1, add_smul, one_smul, hl, hs c hc,
      add_smul, one_smul, hr]
  let d : K := (1+c)⁻¹ - (1+c⁻¹)
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hy : y.toAdd = (1+c)⁻¹ • (d⁻¹ • y.toAdd) +
      -((1+c⁻¹) • (d⁻¹ • y.toAdd)) := by
    rw [← sub_eq_add_neg, ← sub_smul, smul_smul]
    change y.toAdd = (d * d⁻¹) • y.toAdd
    rw [mul_inv_cancel₀ hd, one_smul]
  rw [hy, hr, hneg, he, mul_inv_cancel]

/-- Averaging the central commutator pairing over the scalar units kills the
norm on the derived group. Thus a fixed derived element is annihilated by
`|Kˣ|`. The additive coordinate may have any dimension over K. -/
public theorem fixed_derived_pow_card_units
    {K V P : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Group P]
    (hK : 4 < Nat.card K) (coordinate : P →* Multiplicative V)
    (hsur : Function.Surjective coordinate) (hker : coordinate.ker ≤ center P)
    (action : Kˣ →* MulAut P)
    (hact : ∀ (t : Kˣ) x,
      coordinate (action t x) = .ofAdd ((t : K) • (coordinate x).toAdd))
    (z : P) (hzd : z ∈ _root_.commutator P)
    (hzfix : ∀ t : Kˣ, action t z = z) : z ^ Nat.card Kˣ = 1 := by
  classical
  let : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hd : _root_.commutator P ≤ center P :=
    (Abelianization.commutator_subset_ker coordinate).trans hker
  let N : center P →* center P := {
    toFun x := ∏ t : Kˣ, centerCongr (action t) x
    map_one' := by simp
    map_mul' x y := by simp [Finset.prod_mul_distrib] }
  have hN (s : Kˣ) (x : center P) : N (centerCongr (action s) x) = N x := by
    change (∏ t : Kˣ, centerCongr (action t) (centerCongr (action s) x)) = _
    apply Fintype.prod_equiv (Equiv.mulRight s)
    intro t
    apply Subtype.ext
    change action t (action s x) = action (t*s) x
    rw [map_mul]
    rfl
  obtain ⟨b, hb⟩ := exists_center_commutator_pairing hd
  let nb : P →* (P →* center P) := {
    toFun x := N.comp (b x)
    map_one' := by ext y; simp
    map_mul' x y := by ext w; simp }
  have hnb (x y : P) : nb x y = N (b x y) := rfl
  have hl : ∀ x ∈ coordinate.ker, nb x = 1 := by
    intro x hx
    apply MonoidHom.ext
    intro y
    change N (b x y) = 1
    have he : b x y = 1 := by
      apply Subtype.ext
      rw [hb]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker hx) y).symm
    rw [he, map_one]
  have hr : ∀ x, coordinate.ker ≤ (nb x).ker := by
    intro x y hy
    change N (b x y) = 1
    have he : b x y = 1 := by
      apply Subtype.ext
      rw [hb]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker hy) x)
    rw [he, map_one]
  obtain ⟨c, hc⟩ := exists_descended_pairing coordinate hsur nb hl hr
  have hinv (t : Kˣ) (x y : Multiplicative V) :
      c (.ofAdd ((t : K) • x.toAdd)) (.ofAdd ((t : K) • y.toAdd)) = c x y := by
    obtain ⟨u, rfl⟩ := hsur x
    obtain ⟨v, rfl⟩ := hsur y
    rw [← hact, ← hact, hc, hc, hnb, hnb]
    have he : b (action t u) (action t v) = centerCongr (action t) (b u v) := by
      apply Subtype.ext
      change (b (action t u) (action t v) : P) = action t (b u v)
      rw [hb, hb, map_commutatorElement]
    rw [he, hN]
  have hc1 := invariant_pairing_eq_one hK c hinv
  have hnD := retraction_kills_derived_of_pairing_trivial hd N (fun x y => by
    have hh := hc x y
    rw [hc1, hnb] at hh
    have he : b x y = ⟨⁅x,y⁆, hd (commutator_mem_commutator (mem_top x) (mem_top y))⟩ :=
      Subtype.ext (hb x y)
    exact he ▸ hh.symm)
  have hnz := hnD ⟨z, hd hzd⟩ hzd
  have hterm (t : Kˣ) : centerCongr (action t) ⟨z, hd hzd⟩ = ⟨z, hd hzd⟩ :=
    Subtype.ext (hzfix t)
  change (∏ t : Kˣ, centerCongr (action t) ⟨z, hd hzd⟩) = 1 at hnz
  simp only [hterm, Finset.prod_const, Finset.card_univ] at hnz
  have hh := congrArg Subtype.val hnz
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, Nat.card_eq_fintype_card] using hh

end CentralExtension.ScalarNorm
