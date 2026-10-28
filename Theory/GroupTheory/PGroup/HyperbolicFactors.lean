module

public import Theory.GroupTheory.PGroup.AnisotropicFactors

/-!
# Hyperbolic factors and their genuine quotient reflections

Two order-sixteen factors generate the special group of order sixty-four.
Their involution frames have distinct nontrivial central commutators. The
reflection fixing the first quotient plane fixes its derived line in the
center, and the second reflection fixes the other line. The exact quotient
fixed spaces are essential: transitivity on the center alone does not
recognize UT₃(F₄), even when the whole symmetric center action is available.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15 and proof of 45.3,
pp.242–243, particularly the no-singular-transvection argument.
-/

@[expose] public section
namespace Theory.GroupTheory
open Subgroup
variable (K : Type*) [Group K]

structure HyperbolicFactors where
  card : Nat.card K = 64
  center_card : Nat.card (center K) = 4
  center_elementary : IsElementaryAbelian 2 (center K)
  square_central : ∀ x : K, x ^ 2 ∈ center K
  A : Subgroup K
  B : Subgroup K
  A_card : Nat.card A = 16
  B_card : Nat.card B = 16
  inf_eq : A ⊓ B = center K
  sup_eq : A ⊔ B = ⊤
  z : center K
  u : center K
  z_ne_one : z ≠ 1
  u_ne_one : u ≠ 1
  distinct : z ≠ u
  centralizer_A : centralizer (A : Set K) = center K

variable {K}

/-- A literal involution generating pair in one of the D₈ × C₂ factors. -/
structure HyperbolicFrame (S : Subgroup K) (t : center K) where
  a : K
  b : K
  a_mem : a ∈ S
  b_mem : b ∈ S
  a_square : a ^ 2 = 1
  b_square : b ^ 2 = 1
  swap : b * a = a * b * (t : K)
  generate : ∀ U : Subgroup K, center K ≤ U → a ∈ U → b ∈ U → S ≤ U

namespace HyperbolicFactors

/-- The first genuine source reflection, including its exact fixed quotient plane. -/
structure FirstActor (F : HyperbolicFactors K) where
  aut : MulAut K
  square : aut ^ 2 = 1
  map_z : aut (F.z : K) = F.z
  map_u : aut (F.u : K) = (F.z * F.u : center K)
  fixed_iff : ∀ x : K, aut x * x⁻¹ ∈ center K ↔ x ∈ F.A

/-- The corresponding reflection for the second source factor. -/
structure SecondActor (F : HyperbolicFactors K) where
  aut : MulAut K
  square : aut ^ 2 = 1
  map_z : aut (F.z : K) = (F.z * F.u : center K)
  map_u : aut (F.u : K) = F.u
  fixed_iff : ∀ x : K, aut x * x⁻¹ ∈ center K ↔ x ∈ F.B

end HyperbolicFactors
end Theory.GroupTheory
