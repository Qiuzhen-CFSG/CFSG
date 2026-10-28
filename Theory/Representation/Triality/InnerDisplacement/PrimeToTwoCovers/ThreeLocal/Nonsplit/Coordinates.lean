module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar coordinates for the nonsplit triality torus

Opposition followed by the D₄ graph-field action fixes exactly the four
simple-coroot tuples (a,b,a⁻ᑫ,aᑫ²), where a has order dividing q³+1 and b
has order dividing q+1. This module proves that scalar parametrization and
its cardinality. It does not embed the scalars in the finite triality group.

The central simple reflection sends (a,b) to (a,Norm(a)/b), with
Norm(a)=a^(q²-q+1). Taking the unique square root on the odd-order second
factor diagonalizes this action. This keeps the unequal cyclic factors;
in particular the scalar group at q=2 has order 27.

Source: the rational-torus conventions of GLS3 §§2.1–2.4,
`refs/KGroup/GLS3/chapter2.tex`, for the calculation underlying §6.1.
-/

@[expose] public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
noncomputable section
abbrev Scalars := AlgebraicClosure (ZMod 2)
abbrev Large (n : ℕ) := rootsOfUnity ((2 ^ n) ^ 3 + 1) Scalars
abbrev Small (n : ℕ) := rootsOfUnity (2 ^ n + 1) Scalars
abbrev Coordinates (n : ℕ) := Large n × Small n

theorem card_large (n : ℕ) (hn : 0 < n) : Nat.card (Large n) = (2 ^ n) ^ 3 + 1 := by
  let : NeZero (((2 ^ n) ^ 3 + 1 : ℕ) : ZMod 2) := ⟨by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    rw [ZMod.natCast_self, zero_pow hn.ne']
    decide⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Scalars _

theorem card_small (n : ℕ) (hn : 0 < n) : Nat.card (Small n) = 2 ^ n + 1 := by
  let : NeZero ((2 ^ n + 1 : ℕ) : ZMod 2) := ⟨by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    rw [ZMod.natCast_self, zero_pow hn.ne']
    decide⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Scalars _

theorem card_coordinates (n : ℕ) (hn : 0 < n) :
    Nat.card (Coordinates n) = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) := by
  rw [Nat.card_prod, card_large n hn, card_small n hn]

def normExponent (n : ℕ) : ℕ := (2 ^ n) ^ 2 - 2 ^ n + 1

theorem normExponent_mul (n : ℕ) : normExponent n * (2 ^ n + 1) = (2 ^ n) ^ 3 + 1 := by
  have h : 2 ^ n ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by decide) _
  dsimp [normExponent]
  nlinarith [Nat.sub_add_cancel h]

def normHom (n : ℕ) : Large n →* Small n where
  toFun a := ⟨(a : Scalarsˣ) ^ normExponent n, by
    change ((a : Scalarsˣ) ^ normExponent n) ^ (2 ^ n + 1) = 1
    rw [← pow_mul, normExponent_mul]
    exact a.property⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' a b := Subtype.ext (mul_pow _ _ _)

def halfHom (n : ℕ) : Small n →* Small n := powMonoidHom (2 ^ (n - 1) + 1)

theorem halfHom_sq (n : ℕ) (hn : 0 < n) (b : Small n) : halfHom n b ^ 2 = b := by
  have he : (2 ^ (n - 1) + 1) * 2 = (2 ^ n + 1) + 1 := by
    have h := pow_succ 2 (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    omega
  have hb : b ^ (2 ^ n + 1) = 1 := Subtype.ext b.property
  change (b ^ (2 ^ (n - 1) + 1)) ^ 2 = b
  rw [← pow_mul, he, pow_add, hb]
  simp

/-- The central reflection in raw simple-coroot coordinates. -/
def reflection (n : ℕ) (a : Coordinates n) : Coordinates n :=
  (a.1, normHom n a.1 * a.2⁻¹)

/-- The odd-order square root of the norm diagonalizes the central reflection. -/
def diagonalize (n : ℕ) : Coordinates n ≃* Coordinates n where
  toFun a := (a.1, halfHom n (normHom n a.1) * a.2)
  invFun a := (a.1, (halfHom n (normHom n a.1))⁻¹ * a.2)
  left_inv a := Prod.ext rfl (inv_mul_cancel_left _ _)
  right_inv a := Prod.ext rfl (mul_inv_cancel_left _ _)
  map_mul' a b := by
    apply Prod.ext
    · rfl
    change halfHom n (normHom n (a.1 * b.1)) * (a.2 * b.2) =
      (halfHom n (normHom n a.1) * a.2) * (halfHom n (normHom n b.1) * b.2)
    simp only [map_mul]
    ac_rfl

theorem reflection_diagonalize (n : ℕ) (hn : 0 < n) (a : Coordinates n) :
    reflection n (diagonalize n a) = diagonalize n (a.1, a.2⁻¹) := by
  apply Prod.ext
  · rfl
  change normHom n a.1 * (halfHom n (normHom n a.1) * a.2)⁻¹ =
    halfHom n (normHom n a.1) * a.2⁻¹
  calc
    _ = halfHom n (normHom n a.1) ^ 2 *
        (halfHom n (normHom n a.1) * a.2)⁻¹ :=
      congrArg (fun z => z * (halfHom n (normHom n a.1) * a.2)⁻¹)
        (halfHom_sq n hn (normHom n a.1)).symm
    _ = _ := by simp [pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- Literal four coroot parameters, in the original order 0,1,2,3. -/
def expand (n : ℕ) (a : Coordinates n) : Fin 4 → Scalarsˣ :=
  ![a.1, a.2, ((a.1 : Scalarsˣ) ^ (2 ^ n))⁻¹, (a.1 : Scalarsˣ) ^ ((2 ^ n) ^ 2)]


theorem expand_injective (n : ℕ) : Function.Injective (expand n) := by
  intro a b h
  exact Prod.ext (Subtype.ext (congrFun h 0)) (Subtype.ext (congrFun h 1))

def expandHom (n : ℕ) : Coordinates n →* (Fin 4 → Scalarsˣ) where
  toFun := expand n
  map_one' := by funext i; fin_cases i <;> simp [expand]
  map_mul' a b := by funext i; fin_cases i <;> simp [expand, mul_pow, mul_comm]

/-- Opposition followed by the graph-field action, in the original node order. -/
def signedTwist (n : ℕ) (a : Fin 4 → Scalarsˣ) : Fin 4 → Scalarsˣ :=
  ![(a 3 ^ (2 ^ n))⁻¹, (a 1 ^ (2 ^ n))⁻¹,
    (a 0 ^ (2 ^ n))⁻¹, (a 2 ^ (2 ^ n))⁻¹]

theorem signedTwist_expand (n : ℕ) (a : Coordinates n) :
    signedTwist n (expand n a) = expand n a := by
  have ha : (a.1 : Scalarsˣ) ^ ((2 ^ n) ^ 3) = (a.1 : Scalarsˣ)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact a.1.property
  have hb : (a.2 : Scalarsˣ) ^ (2 ^ n) = (a.2 : Scalarsˣ)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact a.2.property
  funext i
  fin_cases i
  · change (((a.1 : Scalarsˣ) ^ ((2 ^ n) ^ 2)) ^ (2 ^ n))⁻¹ = a.1
    rw [← pow_mul (a.1 : Scalarsˣ), show (2 ^ n) ^ 2 * 2 ^ n = (2 ^ n) ^ 3 by ring,
      ha, inv_inv]
  · change ((a.2 : Scalarsˣ) ^ (2 ^ n))⁻¹ = a.2
    rw [hb, inv_inv]
  · rfl
  · change ((((a.1 : Scalarsˣ) ^ (2 ^ n))⁻¹) ^ (2 ^ n))⁻¹ =
      (a.1 : Scalarsˣ) ^ ((2 ^ n) ^ 2)
    rw [inv_pow, inv_inv, ← pow_mul (a.1 : Scalarsˣ), pow_two]

/-- All fixed scalar tuples have the displayed norm-one coordinates. -/
theorem exists_expand_of_signedTwist (n : ℕ) (a : Fin 4 → Scalarsˣ)
    (ha : signedTwist n a = a) : ∃ b : Coordinates n, expand n b = a := by
  have h0 : (a 3 ^ (2 ^ n))⁻¹ = a 0 := congrFun ha 0
  have h1 : (a 1 ^ (2 ^ n))⁻¹ = a 1 := congrFun ha 1
  have h2 : (a 0 ^ (2 ^ n))⁻¹ = a 2 := congrFun ha 2
  have h3 : (a 2 ^ (2 ^ n))⁻¹ = a 3 := congrFun ha 3
  have h3' : a 0 ^ ((2 ^ n) ^ 2) = a 3 := by
    calc
      _ = (a 0 ^ (2 ^ n)) ^ (2 ^ n) := by rw [← pow_mul (a 0), pow_two]
      _ = (a 2 ^ (2 ^ n))⁻¹ := by rw [← h2, inv_pow, inv_inv]
      _ = a 3 := h3
  have hlarge : a 0 ^ ((2 ^ n) ^ 3 + 1) = 1 := by
    have hh' : (a 0 ^ ((2 ^ n) ^ 3))⁻¹ = a 0 := by
      calc
        _ = ((a 0 ^ ((2 ^ n) ^ 2)) ^ (2 ^ n))⁻¹ := by
          rw [← pow_mul (a 0), show (2 ^ n) ^ 2 * 2 ^ n = (2 ^ n) ^ 3 by ring]
        _ = (a 3 ^ (2 ^ n))⁻¹ := congrArg (fun z => (z ^ (2 ^ n))⁻¹) h3'
        _ = a 0 := h0
    have hh : a 0 ^ ((2 ^ n) ^ 3) = (a 0)⁻¹ := by
      simpa only [inv_inv] using congrArg Inv.inv hh'
    rw [pow_succ, hh, inv_mul_cancel]
  have hsmall : a 1 ^ (2 ^ n + 1) = 1 := by
    have hh : a 1 ^ (2 ^ n) = (a 1)⁻¹ := by
      simpa only [inv_inv] using congrArg Inv.inv h1
    rw [pow_succ, hh, inv_mul_cancel]
  refine ⟨(⟨a 0, hlarge⟩, ⟨a 1, hsmall⟩), ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact h2
  · exact h3'

theorem signedTwist_eq_self_iff (n : ℕ) (a : Fin 4 → Scalarsˣ) :
    signedTwist n a = a ↔ ∃ b : Coordinates n, expand n b = a := by
  constructor
  · exact exists_expand_of_signedTwist n a
  · rintro ⟨b, rfl⟩
    exact signedTwist_expand n b

/-- In particular the scalar torus at q=2 has order 27, not nine. -/
theorem card_coordinates_at_two : Nat.card (Coordinates 1) = 27 := by
  rw [card_coordinates 1 (by decide)]
  norm_num

end
end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
