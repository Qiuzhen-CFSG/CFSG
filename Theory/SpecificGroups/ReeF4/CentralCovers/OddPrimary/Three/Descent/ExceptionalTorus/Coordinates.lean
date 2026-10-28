module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Data
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Faithful coordinates for the marked Ree torus

Put `s = (-2)^m`. In positive simple-coroot coordinates the marking is
`(a*b², b³, b²*(a*b)^s, b^(1+s))`. Since `s ≡ 1 (mod 3)`, the first,
second and fourth coordinates recover both parameters. This proves
faithfulness on every commutative group, including its scalar three-center.
For norm-one parameters, `q = 2*s²` gives the displayed twisted fixed-point
equation. The algebraic diagonal convention uses the inverse tuple.

The negative sign in `s` is essential: using `2^m` for every m would kill
the scalar three-center when m is odd. `coordinates_scalar` records its
actual image `(1,1,z,z²)`.

Source: the A₂×A₂ subsystem in GLS3 Example 2.6.3 and the universal unitary
version in Table 4.7.3A; the concrete coroot identification is in `Roots`.
-/

@[expose] public section
open Theory.AlgebraicGroup
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
noncomputable section

def signedExponent (m : ℕ) : ℤ := (-2) ^ m

def recoveryExponent : ℕ → ℤ
  | 0 => 0
  | m + 1 => -2 * recoveryExponent m - 1

theorem signedExponent_eq (m : ℕ) : signedExponent m = 3 * recoveryExponent m + 1 := by
  induction m with
  | zero => norm_num [signedExponent, recoveryExponent]
  | succ m ih =>
    simp only [signedExponent, pow_succ] at *
    rw [ih]
    simp only [recoveryExponent]
    ring

variable {A : Type*} [CommGroup A]

def coordinates (m : ℕ) (a b : A) : Fin 4 → A :=
  ![a * b ^ 2, b ^ 3, b ^ 2 * (a * b) ^ signedExponent m, b ^ (1 + signedExponent m)]

def coordinateHom (m : ℕ) : (A × A) →* (Fin 4 → A) where
  toFun x := coordinates m x.1 x.2
  map_one' := by ext i; fin_cases i <;> simp [coordinates]
  map_mul' x y := by
    ext i
    fin_cases i <;> simp [coordinates, mul_pow, mul_zpow] <;> ac_rfl

theorem recover_second (m : ℕ) (a b : A) :
    (coordinates m a b 1) ^ (recoveryExponent m + 1) *
      (coordinates m a b 3)⁻¹ = b := by
  change (b ^ (3 : ℕ)) ^ (recoveryExponent m + 1) * (b ^ (1 + signedExponent m))⁻¹ = b
  rw [← zpow_natCast b 3, ← zpow_mul, ← zpow_neg, ← zpow_add]
  have he : (3 : ℤ) * (recoveryExponent m + 1) + -(1 + signedExponent m) = 1 := by
    rw [signedExponent_eq]
    ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he, zpow_one]

theorem coordinateHom_injective (m : ℕ) : Function.Injective (coordinateHom (A := A) m) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : b = d := by
    rw [← recover_second m a b, ← recover_second m c d]
    exact congrArg (fun v : Fin 4 → A => v 1 ^ (recoveryExponent m + 1) * (v 3)⁻¹) h
  subst d
  have ha := congrFun h 0
  change a * b ^ 2 = c * b ^ 2 at ha
  exact Prod.ext (mul_right_cancel ha) rfl


/-- The scalar three-center survives the marking, independently of m. -/
theorem coordinates_scalar (m : ℕ) (z : A) (hz : z ^ (3 : ℕ) = 1) :
    coordinates m z z = ![1, 1, z, z ^ (2 : ℕ)] := by
  have he : z ^ signedExponent m = z := by
    rw [signedExponent_eq, zpow_add, zpow_mul, zpow_ofNat, hz]
    simp
  have h4 : z ^ (4 : ℕ) = z := by rw [show 4 = 3+1 by decide, pow_succ, hz, one_mul]
  ext i
  fin_cases i
  · change z * z ^ 2 = 1
    rw [← pow_succ']
    exact hz
  · exact hz
  · change z ^ 2 * (z * z) ^ signedExponent m = z
    rw [mul_zpow, he, ← pow_two, ← pow_add]
    exact h4
  · change z ^ (1 + signedExponent m) = z ^ (2 : ℕ)
    rw [zpow_add, zpow_one, he, pow_two]


def twistedCoordinates (s : ℤ) : (Fin 4 → A) →* (Fin 4 → A) where
  toFun u := ![u 1 ^ (2*s) * u 2 ^ (-2*s) * u 3 ^ (-2*s),
    u 1 ^ (2*s) * u 3 ^ (-6*s),
    u 0 ^ s * u 1 ^ s * u 3 ^ (-4*s), u 1 ^ s * u 3 ^ (-2*s)]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' u v := by ext i; fin_cases i <;> simp [mul_zpow] <;> ac_rfl

theorem coordinates_fixed (m : ℕ) (a b : A)
    (ha : a ^ (2 * signedExponent m ^ 2 + 1) = 1)
    (hb : b ^ (2 * signedExponent m ^ 2 + 1) = 1) :
    twistedCoordinates (signedExponent m) (coordinates m a b) = coordinates m a b := by
  have h (i : Fin 4) :
      twistedCoordinates (signedExponent m) (coordinates m a b) i =
        coordinates m a b i *
          (a ^ (2 * signedExponent m ^ 2 + 1)) ^ (![(-1 : ℤ), 0, 0, 0] i) *
          (b ^ (2 * signedExponent m ^ 2 + 1)) ^ (![(-2 : ℤ), -3, -2, -1] i) := by
    let s := signedExponent m
    fin_cases i
    · change (b ^ (3 : ℕ)) ^ (2*s) * (b ^ (2 : ℕ) * (a*b)^s) ^ (-2*s) *
        (b^(1+s))^(-2*s) =
          (a*b^(2 : ℕ)) * (a^(2*s^2+1))^(-1 : ℤ) * (b^(2*s^2+1))^(-2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
      module
    · change (b ^ (3 : ℕ)) ^ (2*s) * (b^(1+s))^(-6*s) =
        b^(3 : ℕ) * (a^(2*s^2+1))^(0 : ℤ) * (b^(2*s^2+1))^(-3 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
      module
    · change (a*b^(2 : ℕ))^s * (b^(3 : ℕ))^s * (b^(1+s))^(-4*s) =
        (b^(2 : ℕ) * (a*b)^s) * (a^(2*s^2+1))^(0 : ℤ) * (b^(2*s^2+1))^(-2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
      module
    · change (b^(3 : ℕ))^s * (b^(1+s))^(-2*s) =
        b^(1+s) * (a^(2*s^2+1))^(0 : ℤ) * (b^(2*s^2+1))^(-1 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
      module
  ext i
  simpa only [ha, hb, one_zpow, mul_one] using h i

theorem signedExponent_square (m : ℕ) :
    2 * signedExponent m ^ 2 = (2 ^ (2 * m + 1) : ℕ) := by
  have h : signedExponent m ^ 2 = (2 : ℤ) ^ (2 * m) := by
    rw [signedExponent, ← pow_mul, mul_comm m 2, pow_mul]
    norm_num only [neg_sq]
    rw [pow_mul]
    norm_num
  calc
    2 * signedExponent m ^ 2 = (2 : ℤ) ^ (2*m+1) := by rw [h, pow_succ']
    _ = _ := by norm_cast

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
