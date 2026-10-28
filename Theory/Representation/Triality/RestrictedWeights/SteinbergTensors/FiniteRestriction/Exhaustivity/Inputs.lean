module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Contracts
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Inputs to the D4 finite exhaustivity argument

The actual restricted integral weights are in bijection with four independent
coordinates in `Fin (2^n)`. The remaining construction and counting obligations
are stated separately from `Geometry`: rational modules with the four
fundamental highest weights, and an odd-order conjugacy-class bound on the
literal elementary graph-field subgroup.

Sources: GLS3, Theorem 2.8.2; `refs/KGroup/GLS3/Chapter2St2.tex`, Sections
13.3(b), 13.5 and 14.8. These definitions do not assert those theorems.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

/-- Integral highest weights in the exact restricted range. -/
abbrev RestrictedWeight (n : ℕ) := {a : Weight // InRestrictedRange n a}

/-- Each of the four integral coordinates is independently in `[0, 2^n)`. -/
def restrictedWeightEquiv (n : ℕ) : RestrictedWeight n ≃ (Fin 4 → Fin (2 ^ n)) where
  toFun a i := ⟨(a.val i).toNat,
    (Int.toNat_lt (a.property i).1).mpr (by exact_mod_cast (a.property i).2)⟩
  invFun b := ⟨fun i => (b i).val, fun i => ⟨by positivity, by
    change ((b i).val : ℤ) < (2 : ℤ) ^ n
    exact_mod_cast (b i).isLt⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact Int.toNat_of_nonneg (a.property i).1
  right_inv b := by
    funext i
    apply Fin.ext
    simp

/-- The restricted range contains `(2^n)^4` actual integral weights. -/
theorem card_restrictedWeight (n : ℕ) : Nat.card (RestrictedWeight n) = (2 ^ n) ^ 4 := by
  rw [Nat.card_congr (restrictedWeightEquiv n)]
  simp [Nat.card_eq_fintype_card]

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Existence of rational irreducibles for all restricted highest weights.
This is an obligation, not a field of the geometric setup. -/
def RestrictedRationalExistence (S : Geometry K) (n : ℕ) : Prop :=
  ∀ a : Weight, InRestrictedRange n a → ∃ A : RationalFactor K, HasHighestWeight S A a

/-- The class-count input concerns the elementary subgroup itself. A bound
for the full fixed-point group requires a proved passage to this subgroup. -/
def ElementaryClassBound (S : Geometry K) (n : ℕ) : Prop :=
  Nat.card (ConjClasses.mk '' {g : graphFieldElementarySubgroup
    S.diagram.toMulEquiv S.frobenius.onPoints n | ¬ 2 ∣ orderOf g}) ≤ (2 ^ n) ^ 4

/-- Only the four fundamental rational highest weights are needed for the
existence construction. No finite restriction or tensor simplicity is assumed. -/
def FundamentalRationalExistence (S : Geometry K) : Prop :=
  ∀ i : Fin 4, ∃ A : RationalFactor K, HasHighestWeight S A (Pi.single i 1)


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
