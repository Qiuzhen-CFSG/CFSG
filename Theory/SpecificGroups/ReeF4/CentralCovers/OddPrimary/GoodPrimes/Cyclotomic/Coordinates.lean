module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Coordinates of the two cyclotomic Ree tori

Write `a = 2^m`. In the simple-coroot coordinates numbered by the standard F4
Cartan matrix, the candidate twist for the Weyl word `s₀s₁` sends
`u` to `(u₁^(2a)u₂^(-2a), u₁^(2a)u₂^(-2a)u₃^(2a), u₁^a, u₀^a)`.
Opposition replaces `a` by `-a`. This module solves these four multiplicative
coordinate equations: projection to coordinate 1 identifies their fixed group
with the roots of unity of order `4a⁴ - 4a³ + 2a² - 2a + 1`.

The two natural orders agree with the integer-field-size convention of the
consumer, including natural subtraction in the minus branch. The identification
of these coordinate maps with actual exceptional/Weyl actions and descent to
`ReeF4.Model` are separate obligations; a coordinate fixed point alone is not
an element of that finite group.

Sources: GLS3, §§2.1–2.4 and §4.10 (`refs/KGroup/GLS3/chapter2.tex` and
`chapter4.tex`), with integer field size `q = 2^(2m+1)`.
-/

public section

open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic

@[expose] def orderPolynomial (a : ℤ) : ℤ := 4*a^4 - 4*a^3 + 2*a^2 - 2*a + 1

/-- The two signed factors multiply to the twelfth cyclotomic factor. -/
theorem orderPolynomial_mul_neg (a : ℤ) :
    orderPolynomial a * orderPolynomial (-a) = (2*a^2)^4 - (2*a^2)^2 + 1 := by
  unfold orderPolynomial
  ring

theorem polynomial_pos (a : ℤ) : 0 < orderPolynomial a := by
  have h : orderPolynomial a = (2*a^2-a)^2 + (a-1)^2 := by
    unfold orderPolynomial
    ring
  rw [h]
  by_contra hn
  have ha : (a-1)^2 = 0 := by nlinarith [sq_nonneg (2*a^2-a), sq_nonneg (a-1)]
  have : a = 1 := by nlinarith [sq_nonneg (a-1)]
  subst a
  norm_num at hn

variable {G : Type*} [CommGroup G]

@[expose] def coordinates (a : ℤ) : G →* (Fin 4 → G) where
  toFun z := ![z ^ (2*a-2*a^2), z, z ^ a, z ^ (2*a^2-2*a^3)]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' z w := by ext i; fin_cases i <;> simp [mul_zpow]

@[expose] def twistedAction (a : ℤ) : (Fin 4 → G) →* (Fin 4 → G) where
  toFun u := ![u 1 ^ (2*a) * u 2 ^ (-2*a),
    u 1 ^ (2*a) * u 2 ^ (-2*a) * u 3 ^ (2*a), u 1 ^ a, u 0 ^ a]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' u v := by
    ext i
    fin_cases i <;> simp [mul_zpow] <;> ac_rfl

theorem coordinates_injective (a : ℤ) : Function.Injective (coordinates (G := G) a) := by
  intro z w h
  exact congrFun h 1

theorem coordinates_fixed (a : ℤ) (z : G) (hz : z ^ orderPolynomial a = 1) :
    twistedAction a (coordinates a z) = coordinates a z := by
  ext i
  fin_cases i
  · change z^(2*a) * (z^a)^(-2*a) = z^(2*a-2*a^2)
    rw [← zpow_mul, ← zpow_add]
    congr 1
    ring
  · change z ^ (2*a) * (z^a)^(-2*a) * (z^(2*a^2-2*a^3))^(2*a) = z
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add]
    have he : 2*a + a*(-2*a) + (2*a^2-2*a^3)*(2*a) = 1-orderPolynomial a := by
      unfold orderPolynomial
      ring
    rw [he, zpow_sub, hz]
    simp
  · rfl
  · change (z^(2*a-2*a^2))^a = z^(2*a^2-2*a^3)
    rw [← zpow_mul]
    congr 1
    ring

theorem fixed_coordinates (a : ℤ) (u : Fin 4 → G)
    (hu : twistedAction a u = u) : coordinates a (u 1) = u := by
  have h0 : u 1 ^ (2*a) * u 2 ^ (-2*a) = u 0 := congrFun hu 0
  have h2 : u 1 ^ a = u 2 := congrFun hu 2
  have h3 : u 0 ^ a = u 3 := congrFun hu 3
  have hc0 : u 0 = (u 1)^(2*a-2*a^2) := by
    rw [← h0, ← h2, ← zpow_mul, ← zpow_add]
    congr 1
    ring
  ext i
  fin_cases i
  · exact hc0.symm
  · rfl
  · exact h2
  · change (u 1)^(2*a^2-2*a^3) = u 3
    rw [← h3, hc0, ← zpow_mul]
    congr 1
    ring

theorem fixed_order (a : ℤ) (u : Fin 4 → G)
    (hu : twistedAction a u = u) : u 1 ^ orderPolynomial a = 1 := by
  have he : u 1 ^ (1-orderPolynomial a) = u 1 := by
    have h := congrFun hu 1
    rw [← fixed_coordinates a u hu] at h
    change u 1 ^ (2*a) * ((u 1)^a)^(-2*a) *
      ((u 1)^(2*a^2-2*a^3))^(2*a) = u 1 at h
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add] at h
    convert h using 2
    unfold orderPolynomial
    ring
  rw [zpow_sub, zpow_one] at he
  have : (u 1 ^ orderPolynomial a)⁻¹ = 1 := mul_left_cancel (he.trans (mul_one _).symm)
  exact inv_eq_one.mp this

end ReeF4.CentralCovers.OddPrimary.Cyclotomic

namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic

def torusOrder (a : ℤ) : ℕ := (orderPolynomial a).toNat

theorem torusOrder_cast (a : ℤ) : (torusOrder a : ℤ) = orderPolynomial a :=
  Int.toNat_of_nonneg (polynomial_pos a).le

theorem torusOrder_pos (a : ℤ) : 0 < torusOrder a := by
  exact_mod_cast (torusOrder_cast a ▸ polynomial_pos a : 0 < (torusOrder a : ℤ))

variable {F : Type*} [Field F]

def rootsCoordinates (a : ℤ) : rootsOfUnity (torusOrder a) F →* (Fin 4 → Fˣ) :=
  (coordinates a).comp (rootsOfUnity (torusOrder a) F).subtype

theorem rootsCoordinates_injective (a : ℤ) :
    Function.Injective (rootsCoordinates (F := F) a) :=
  (coordinates_injective a).comp Subtype.val_injective

theorem rootsCoordinates_fixed (a : ℤ) (z : rootsOfUnity (torusOrder a) F) :
    twistedAction a (rootsCoordinates a z) = rootsCoordinates a z := by
  apply coordinates_fixed
  rw [← torusOrder_cast, zpow_natCast]
  exact (mem_rootsOfUnity _ _).mp z.property

@[expose] def fixedCoordinates (a : ℤ) : Subgroup (Fin 4 → Fˣ) :=
  MonoidHom.eqLocus (twistedAction a) (MonoidHom.id _)

def rootsFixedEquiv (a : ℤ) : rootsOfUnity (torusOrder a) F ≃* fixedCoordinates (F := F) a where
  toFun z := ⟨rootsCoordinates a z, rootsCoordinates_fixed a z⟩
  invFun u := ⟨u.val 1, by
    rw [mem_rootsOfUnity, ← zpow_natCast, torusOrder_cast]
    exact fixed_order a u.val u.property⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; exact fixed_coordinates a u.val u.property
  map_mul' z w := by apply Subtype.ext; exact map_mul (rootsCoordinates a) z w

@[expose] def minusOrder (m : ℕ) : ℕ :=
  (2^(2*m+1))^2 + 2^(2*m+1) + 1 - 2^(m+1)*(2^(2*m+1)+1)

@[expose] def plusOrder (m : ℕ) : ℕ :=
  (2^(2*m+1))^2 + 2^(2*m+1) + 1 + 2^(m+1)*(2^(2*m+1)+1)

theorem minusOrder_eq (m : ℕ) : minusOrder m = torusOrder (2^m) := by
  have hq : (2:ℕ)^(2*m+1) = 2*(2^m)^2 := by
    rw [pow_succ, Nat.mul_comm 2 m, pow_mul]
    ring
  have ht : (2:ℕ)^(m+1) = 2*2^m := by rw [pow_succ]; ring
  have hpos := polynomial_pos ((2:ℤ)^m)
  have hbound : 2^(m+1)*(2^(2*m+1)+1) ≤ (2^(2*m+1))^2 + 2^(2*m+1) + 1 := by
    rw [hq, ht]
    zify
    norm_cast at hpos ⊢
    unfold orderPolynomial at hpos
    nlinarith
  apply Int.natCast_inj.mp
  rw [minusOrder, Int.natCast_sub hbound, torusOrder_cast]
  push_cast
  rw [show (2:ℤ)^(2*m+1) = 2*(2^m)^2 by
    rw [pow_succ, Nat.mul_comm 2 m, pow_mul]; ring,
    show (2:ℤ)^(m+1) = 2*2^m by rw [pow_succ]; ring]
  unfold orderPolynomial
  ring

theorem plusOrder_eq (m : ℕ) : plusOrder m = torusOrder (-(2^m)) := by
  apply Int.natCast_inj.mp
  rw [plusOrder, torusOrder_cast]
  push_cast
  rw [show (2:ℤ)^(2*m+1) = 2*(2^m)^2 by
    rw [pow_succ, Nat.mul_comm 2 m, pow_mul]; ring,
    show (2:ℤ)^(m+1) = 2*2^m by rw [pow_succ]; ring]
  unfold orderPolynomial
  ring

theorem minusOrder_pos (m : ℕ) : 0 < minusOrder m := by
  rw [minusOrder_eq]
  exact torusOrder_pos _

theorem plusOrder_pos (m : ℕ) : 0 < plusOrder m := by
  rw [plusOrder_eq]
  exact torusOrder_pos _

/-- The source's smallest large Ree parameter has cyclotomic orders 37 and 109. -/
theorem orders_at_eight : minusOrder 1 = 37 ∧ plusOrder 1 = 109 := by
  norm_num [minusOrder, plusOrder]

end ReeF4.CentralCovers.OddPrimary.Cyclotomic
