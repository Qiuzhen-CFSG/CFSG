module
public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Normal forms and linear characters of the modular group of order sixteen

In a group of order sixteen, elements f and x with |f| = 8, x² = 1,
and xfx⁻¹ = f⁵ give unique coordinates fⁱxʲ (i < 8, j < 2). For any
complex a and b with a⁴ = b² = 1, these coordinates define a homomorphism
sending f to a and x to b. Coordinates also lift uniquely through any
normal subgroup by appending an element of the kernel.

The nontrivial conjugation action puts x outside ⟨f⟩. Cancellation proves
coordinate injectivity; cardinality gives surjectivity. The conjugation
relation verifies the character multiplication formula, since a⁵ = a.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization
of U(3,3), J. Algebra 6 (1967), printed p. 72, first two paragraphs.
-/

namespace ModularSixteen
variable {K : Type*} [Group K] [Finite K] (f x : K)
  (hf : orderOf f = 8) (hx : x ^ 2 = 1) (hxf : x * f * x⁻¹ = f ^ 5)

@[expose] public def normalForm (p : Fin 8 × Fin 2) : K := f ^ p.1.val * x ^ p.2.val

omit [Finite K] in
include hf hxf in
private theorem x_not_zpower (n : ℤ) : x ≠ f ^ n := by
  intro he
  have hc : x * f * x⁻¹ = f := by rw [he]; group
  have hp : f ^ 5 = f ^ 1 := by simpa only [pow_one] using hxf.symm.trans hc
  have hi := pow_inj_mod.mp hp
  norm_num [hf] at hi

omit [Finite K] in
include hf hxf in
public theorem normalForm_injective : Function.Injective (normalForm f x) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hj : j = l := by
    by_contra hne
    fin_cases j <;> fin_cases l
    · exact hne rfl
    · simp only [normalForm, pow_zero, pow_one, mul_one] at he
      apply x_not_zpower f x hf hxf ((i.val : ℤ) - k.val)
      calc
        x = (f ^ k.val)⁻¹ * f ^ i.val := (eq_inv_mul_iff_mul_eq).mpr he.symm
        _ = f ^ ((i.val : ℤ) - k.val) := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
          congr 1
          omega
    · simp only [normalForm, pow_zero, pow_one, mul_one] at he
      apply x_not_zpower f x hf hxf ((k.val : ℤ) - i.val)
      calc
        x = (f ^ i.val)⁻¹ * f ^ k.val := (eq_inv_mul_iff_mul_eq).mpr he
        _ = f ^ ((k.val : ℤ) - i.val) := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
          congr 1
          omega
    · exact hne rfl
  subst l
  have hi : i = k := by
    apply Fin.ext
    have hp : f ^ i.val = f ^ k.val := mul_right_cancel he
    have hi := pow_inj_mod.mp hp
    simpa only [hf, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt k.isLt] using hi
  subst k
  rfl

include hf hxf in
public theorem normalForm_bijective (hcard : Nat.card K = 16) :
    Function.Bijective (normalForm f x) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨normalForm_injective f x hf hxf, by simp [hcard]⟩


private noncomputable def coordinateEquiv (hcard : Nat.card K = 16) :
    (Fin 8 × Fin 2) ≃ K := Equiv.ofBijective _ (normalForm_bijective f x hf hxf hcard)

private noncomputable def characterValue (hcard : Nat.card K = 16) (a b : ℂ) (g : K) : ℂ :=
  a ^ ((coordinateEquiv f x hf hxf hcard).symm g).1.val *
    b ^ ((coordinateEquiv f x hf hxf hcard).symm g).2.val

private theorem characterValue_normalForm (hcard : Nat.card K = 16)
    (a b : ℂ) (i : Fin 8) (j : Fin 2) :
    characterValue f x hf hxf hcard a b (f ^ i.val * x ^ j.val) = a ^ i.val * b ^ j.val := by
  change a ^ ((coordinateEquiv f x hf hxf hcard).symm
    ((coordinateEquiv f x hf hxf hcard) (i,j))).1.val *
    b ^ ((coordinateEquiv f x hf hxf hcard).symm
    ((coordinateEquiv f x hf hxf hcard) (i,j))).2.val = _
  rw [Equiv.symm_apply_apply]

include hx in
private theorem characterValue_powers (hcard : Nat.card K = 16)
    (a b : ℂ) (ha : a ^ 4 = 1) (hb : b ^ 2 = 1) (i j : ℕ) :
    characterValue f x hf hxf hcard a b (f ^ i * x ^ j) = a ^ i * b ^ j := by
  have hf8 : f ^ 8 = 1 := hf ▸ pow_orderOf_eq_one f
  have ha8 : a ^ 8 = 1 := by rw [show 8 = 4 * 2 from rfl, pow_mul, ha, one_pow]
  rw [pow_eq_pow_mod i hf8, pow_eq_pow_mod j hx]
  rw [characterValue_normalForm f x hf hxf hcard a b
    (⟨i % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
    (⟨j % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)]
  exact congrArg₂ (· * ·) (pow_eq_pow_mod i ha8).symm (pow_eq_pow_mod j hb).symm

omit [Finite K] in
include hxf in
private theorem swap_power (n : ℕ) : x * f ^ n = f ^ (5 * n) * x := by
  have hh := map_pow (MulAut.conj x) f n
  change x * f ^ n * x⁻¹ = (x * f * x⁻¹) ^ n at hh
  rw [hxf, ← pow_mul] at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

include hx in
public noncomputable def character (hcard : Nat.card K = 16)
    (a b : ℂ) (ha : a ^ 4 = 1) (hb : b ^ 2 = 1) : K →* ℂ where
  toFun := characterValue f x hf hxf hcard a b
  map_one' := by
    simpa only [pow_zero, one_mul] using
      characterValue_powers f x hf hx hxf hcard a b ha hb 0 0
  map_mul' g h := by
    obtain ⟨⟨i,j⟩, rfl⟩ := (normalForm_bijective f x hf hxf hcard).surjective g
    obtain ⟨⟨k,l⟩, rfl⟩ := (normalForm_bijective f x hf hxf hcard).surjective h
    change characterValue f x hf hxf hcard a b
      ((f ^ i.val * x ^ j.val) * (f ^ k.val * x ^ l.val)) = _
    dsimp only [normalForm]
    rw [characterValue_normalForm, characterValue_normalForm]
    fin_cases j
    · simp only [pow_zero, mul_one]
      rw [← mul_assoc, ← pow_add,
        characterValue_powers f x hf hx hxf hcard a b ha hb]
      rw [pow_add]
      ring
    · simp only [pow_one]
      have he : (f ^ i.val * x) * (f ^ k.val * x ^ l.val) =
          f ^ (i.val + 5 * k.val) * x ^ (1 + l.val) := by
        rw [pow_add, pow_add, pow_one]
        calc
          _ = f ^ i.val * (x * f ^ k.val) * x ^ l.val := by group
          _ = _ := by rw [swap_power f x hxf]; group
      rw [he, characterValue_powers f x hf hx hxf hcard a b ha hb,
        pow_add, pow_mul, pow_add, pow_one]
      have ha5 : a ^ 5 = a := by rw [show 5 = 4 + 1 from rfl, pow_add, ha, pow_one, one_mul]
      rw [ha5]
      ring

public theorem character_f (hcard : Nat.card K = 16)
    (a b : ℂ) (ha : a ^ 4 = 1) (hb : b ^ 2 = 1) :
    character f x hf hx hxf hcard a b ha hb f = a := by
  change characterValue f x hf hxf hcard a b f = a
  have hh := characterValue_normalForm f x hf hxf hcard a b (1 : Fin 8) (0 : Fin 2)
  simpa only [Fin.val_one, Fin.val_zero, pow_zero, pow_one, mul_one] using hh

public theorem character_x (hcard : Nat.card K = 16)
    (a b : ℂ) (ha : a ^ 4 = 1) (hb : b ^ 2 = 1) :
    character f x hf hx hxf hcard a b ha hb x = b := by
  change characterValue f x hf hxf hcard a b x = b
  have hh := characterValue_normalForm f x hf hxf hcard a b (0 : Fin 8) (1 : Fin 2)
  simpa only [Fin.val_one, Fin.val_zero, pow_zero, pow_one, one_mul] using hh

variable {H : Type*} [Group H] (U : Subgroup H) [U.Normal] (f x : H)

public theorem quotient_normalForm_lift
    (hn : Function.Bijective (fun p : Fin 8 × Fin 2 =>
      (QuotientGroup.mk' U f) ^ p.1.val * (QuotientGroup.mk' U x) ^ p.2.val)) :
    Function.Bijective (fun p : Fin 8 × Fin 2 × U => f ^ p.1.val * x ^ p.2.1.val * p.2.2.val) := by
  let q := QuotientGroup.mk' U
  constructor
  · rintro ⟨i,j,u⟩ ⟨k,l,v⟩ he
    have hq := congrArg q he
    have hu : q u.val = 1 := (QuotientGroup.eq_one_iff u.val).mpr u.property
    have hv : q v.val = 1 := (QuotientGroup.eq_one_iff v.val).mpr v.property
    simp only [map_mul, map_pow, hu, hv, mul_one] at hq
    have hij : (i,j) = (k,l) := hn.injective hq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
    have huv : u = v := Subtype.ext (mul_left_cancel he)
    subst v
    rfl
  · intro h
    obtain ⟨⟨i,j⟩, he⟩ := hn.surjective (q h)
    change q f ^ i.val * q x ^ j.val = q h at he
    have hu : (f ^ i.val * x ^ j.val)⁻¹ * h ∈ U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((f ^ i.val * x ^ j.val)⁻¹ * h) = 1
      rw [map_mul, map_inv, map_mul, map_pow, map_pow, he, inv_mul_cancel]
    exact ⟨(i,j,⟨(f ^ i.val * x ^ j.val)⁻¹ * h,hu⟩), mul_inv_cancel_left _ h⟩
end ModularSixteen
