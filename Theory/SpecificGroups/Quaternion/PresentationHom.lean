module
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# Homomorphisms from the quaternion presentation

Elements a,b satisfying a^4=1, b^2=a^2 and ba=a^-1b determine a
homomorphism from the quaternion group of order eight. The fourth-power
hypothesis allows degenerations where the central involution maps to one;
no injectivity or exact element order is assumed.

A cyclic power homomorphism is constructed by the universal property of
ZMod. The quaternion normal forms a^i and b*a^i then multiply according
to the defining relations. Public generator-evaluation lemmas describe
the resulting homomorphism without exposing its normal-form implementation.
This is used in constructing the binary-tetrahedral image in central
extensions of A4 with arbitrary two-kernel.

The normal-form proof is adapted from the private abstractQ8Hom calculation
in `Theory/Alternating/proposition_5_2_6.lean` (GLS3 5.2.6), replacing its
exact-order-four cyclic equivalence by the general ZMod power map.
-/

public section

namespace QuaternionGroup

def cyclicPowerHom {E : Type*} [Group E] (n : ℕ) (a : E) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* E :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift n ⟨zmultiplesHom (Additive E) (Additive.ofMul a), by
      apply Additive.toMul.injective
      change a ^ (n : ℤ) = 1
      rw [zpow_natCast]
      exact ha⟩)

theorem cyclicPowerHom_intCast {E : Type*} [Group E]
    (n : ℕ) (a : E) (ha : a ^ n = 1) (i : ℤ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (i : ZMod n)) = a ^ i := by
  simp [cyclicPowerHom]

theorem cyclicPowerHom_one {E : Type*} [Group E]
    (n : ℕ) (a : E) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  simpa using cyclicPowerHom_intCast n a ha 1


private theorem cyclicPowerHom_mem_zpowers {E : Type*} [Group E]
    (a : E) (ha : a ^ 4 = 1) (i : ZMod 4) :
    cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) ∈ Subgroup.zpowers a := by
  have h := cyclicPowerHom_intCast 4 a ha (i.val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
  rw [h]
  exact Subgroup.zpow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) _

private theorem cyclicPowerHom_two {E : Type*} [Group E]
    (a : E) (ha : a ^ 4 = 1) :
    cyclicPowerHom 4 a ha (Multiplicative.ofAdd 2) = a ^ 2 := by
  simpa using cyclicPowerHom_intCast 4 a ha 2

private theorem cyclicFourHom_b_mul {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hba : b * a = a⁻¹ * b)
    (i : ZMod 4) :
    b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) =
      cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i)) * b := by
  obtain ⟨z, hz⟩ := cyclicPowerHom_mem_zpowers a ha i
  calc
    b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) = b * a ^ z := by rw [← hz]
    _ = (a⁻¹) ^ z * b :=
      (show SemiconjBy b a a⁻¹ from hba).zpow_right z
    _ = (a ^ z)⁻¹ * b := by rw [inv_zpow]
    _ = (cyclicPowerHom 4 a ha (Multiplicative.ofAdd i))⁻¹ * b := by rw [← hz]
    _ = cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i)) * b := by
      rw [← map_inv]
      rfl

private theorem cyclicFourHom_mul_b {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hba : b * a = a⁻¹ * b)
    (i : ZMod 4) :
    cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) * b =
      b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i)) := by
  have h := cyclicFourHom_b_mul a b ha hba (-i)
  simpa using h.symm

private def abstractQ8Map {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) : QuaternionGroup 2 → E
  | .a i => cyclicPowerHom 4 a ha (Multiplicative.ofAdd i)
  | .xa i => b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i)

private theorem abstractQ8Map_one
    {E : Type*} [Group E] (a b : E) (ha : a ^ 4 = 1) :
    abstractQ8Map a b ha 1 = 1 := by
  change cyclicPowerHom 4 a ha (Multiplicative.ofAdd 0) = 1
  exact map_one _

private theorem abstractQ8Map_mul
    {E : Type*} [Group E] (a b : E)
    (ha : a ^ 4 = 1) (hb2 : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b)
    (x y : QuaternionGroup 2) :
    abstractQ8Map a b ha (x * y) =
      abstractQ8Map a b ha x * abstractQ8Map a b ha y := by
  rcases x with i | i <;> rcases y with j | j
  · change cyclicPowerHom 4 a ha (Multiplicative.ofAdd (i + j)) =
      cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) *
        cyclicPowerHom 4 a ha (Multiplicative.ofAdd j)
    exact map_mul _ _ _
  · change b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd (j - i)) =
      cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) *
        (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd j))
    rw [← mul_assoc, cyclicFourHom_mul_b a b ha hba i, mul_assoc, ← map_mul]
    congr 2
    apply Multiplicative.toAdd.injective
    change j - i = -i + j
    ring
  · change b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd (i + j)) =
      (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i)) *
        cyclicPowerHom 4 a ha (Multiplicative.ofAdd j)
    rw [mul_assoc, ← map_mul]
    congr 2
  · change cyclicPowerHom 4 a ha (Multiplicative.ofAdd (2 + j - i)) =
      (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i)) *
        (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd j))
    symm
    calc
      (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd i)) *
          (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd j)) =
          b * (cyclicPowerHom 4 a ha (Multiplicative.ofAdd i) * b) *
            cyclicPowerHom 4 a ha (Multiplicative.ofAdd j) := by group
      _ = b * (b * cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i))) *
            cyclicPowerHom 4 a ha (Multiplicative.ofAdd j) := by
              rw [cyclicFourHom_mul_b a b ha hba i]
      _ = b ^ 2 * cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i)) *
            cyclicPowerHom 4 a ha (Multiplicative.ofAdd j) := by
              rw [pow_two]
              group
      _ = cyclicPowerHom 4 a ha (Multiplicative.ofAdd 2) *
            cyclicPowerHom 4 a ha (Multiplicative.ofAdd (-i)) *
            cyclicPowerHom 4 a ha (Multiplicative.ofAdd j) := by
              rw [hb2, cyclicPowerHom_two]
      _ = cyclicPowerHom 4 a ha (Multiplicative.ofAdd (2 + j - i)) := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Multiplicative.toAdd.injective
        simp
        ring

def liftOfRelations {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hb2 : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) : QuaternionGroup 2 →* E where
  toFun := abstractQ8Map a b ha
  map_one' := abstractQ8Map_one a b ha
  map_mul' := abstractQ8Map_mul a b ha hb2 hba


@[simp] theorem liftOfRelations_a_one {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hb : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) :
    liftOfRelations a b ha hb hba (QuaternionGroup.a 1) = a := by
  exact cyclicPowerHom_one 4 a ha

@[simp] theorem liftOfRelations_xa_zero {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hb : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) :
    liftOfRelations a b ha hb hba (QuaternionGroup.xa 0) = b := by
  change b * cyclicPowerHom 4 a ha 1 = b
  rw [map_one, mul_one]

/-- The quaternion presentation defines a homomorphism even when the
central involution degenerates to the identity. -/
theorem exists_hom_of_relations {E : Type*} [Group E]
    (a b : E) (ha : a ^ 4 = 1) (hb : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) :
    ∃ f : QuaternionGroup 2 →* E,
      f (QuaternionGroup.a 1) = a ∧ f (QuaternionGroup.xa 0) = b :=
  ⟨liftOfRelations a b ha hb hba,
    liftOfRelations_a_one a b ha hb hba,
    liftOfRelations_xa_zero a b ha hb hba⟩

end QuaternionGroup

