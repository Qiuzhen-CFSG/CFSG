module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Index
public import Theory.ElementaryAbelian.Basic

/-!
# The elementary subgroups in the local product of 15.3.61

The printed proof on p.1150 says that two `E₁₆` subgroups cover the
involutions of `U_a V`, after specifying `U_a ≃ E₄ × D₈`. With the source's
central elementary extension by `V`, the local product is `E₈ × D₈`.
This module checks its 48 square-one elements and constructs the two
covering elementary abelian subgroups of order 32. Two subgroups of order
16 cannot cover its involutions.

The obstruction transports only along an actual multiplicative equivalence.
The source application still has to construct that equivalence from the
local intersections and centralization; an order-64 identification alone
is not used. The intermediate `E₁₆` should be `E₃₂` in this model; the
statements of 15.3.59–61 and the final fusion target are unchanged.
All finite calculations below use kernel-checked `decide`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1150.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
variable {G : Type*} [Group G] [Finite G]

/-- The square-one elements covered by two subgroups cannot outnumber their sum. -/
theorem square_one_card_le_of_involution_cover (A B : Subgroup G)
    (hcover : ∀ x : G, orderOf x = 2 → x ∈ A ∨ x ∈ B) :
    Nat.card {x : G // x ^ 2 = 1} ≤ Nat.card A + Nat.card B := by
  classical
  have hc (x : {x : G // x ^ 2 = 1}) : (x : G) ∈ A ∨ (x : G) ∈ B := by
    by_cases hx : (x : G) = 1
    · exact Or.inl (by rw [hx]; exact A.one_mem)
    · exact hcover x (orderOf_eq_prime x.property hx)
  let f : {x : G // x ^ 2 = 1} → A ⊕ B := fun x =>
    if ha : (x : G) ∈ A then Sum.inl ⟨x, ha⟩ else Sum.inr ⟨x, (hc x).resolve_left ha⟩
  let back : A ⊕ B → G := Sum.elim Subtype.val Subtype.val
  have hf (x) : back (f x) = x := by
    dsimp [f]
    split_ifs <;> rfl
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg back h).trans (hf y))
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective f hinj

/-- The local product forced by `U_a ≃ E₄ × D₈` and the central elementary
extension by `V` has order 64. -/
abbrev CentralProductModel := Multiplicative (Fin 3 → ZMod 2) × DihedralGroup 4

theorem centralProductModel_card : Nat.card CentralProductModel = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- There are 47 involutions and the identity in `E₈ × D₈`. -/
theorem centralProductModel_square_one_card :
    Nat.card {x : CentralProductModel // x ^ 2 = 1} = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Consequently the printed two-`E₁₆` cover in the proof of 15.3.61 cannot
hold in this local product. The cover must use the two `E₃₂` subgroups. -/
theorem centralProductModel_no_two_sixteen_cover
    (A B : Subgroup CentralProductModel) (hA : Nat.card A = 16) (hB : Nat.card B = 16) :
    ¬ (∀ x : CentralProductModel, orderOf x = 2 → x ∈ A ∨ x ∈ B) := by
  intro hcover
  have h := square_one_card_le_of_involution_cover A B hcover
  rw [centralProductModel_square_one_card, hA, hB] at h
  omega

private def planePredicate (e : Fin 2) (d : DihedralGroup 4) : Bool :=
  match d with
  | .r i => decide (i.val % 2 = 0)
  | .sr i => decide (i.val % 2 = e.val)

private def dihedralPlane (e : Fin 2) : Subgroup (DihedralGroup 4) where
  carrier := {d | planePredicate e d = true}
  one_mem' := by revert e; decide
  mul_mem' := by
    change ∀ a b, planePredicate e a = true → planePredicate e b = true →
      planePredicate e (a * b) = true
    revert e
    decide
  inv_mem' := by
    change ∀ a, planePredicate e a = true → planePredicate e a⁻¹ = true
    revert e
    decide

/-- The two actual elementary abelian subgroups covering all involutions. -/
def modelPlane (e : Fin 2) : Subgroup CentralProductModel :=
  (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).prod (dihedralPlane e)

private instance (e : Fin 2) : DecidablePred (· ∈ modelPlane e) := fun x =>
  inferInstanceAs (Decidable (True ∧ planePredicate e x.2 = true))

theorem modelPlane_card (e : Fin 2) : Nat.card (modelPlane e) = 32 := by
  rw [Nat.card_eq_fintype_card]
  revert e
  decide

theorem modelPlane_square_one (e : Fin 2) : ∀ x ∈ modelPlane e, x ^ 2 = 1 := by
  revert e
  decide

/-- Each of the two order-32 subgroups is elementary abelian. -/
theorem modelPlane_elementary (e : Fin 2) : IsElementaryAbelian 2 (modelPlane e) := by
  have hs (x : modelPlane e) : x ^ 2 = 1 :=
    Subtype.ext (modelPlane_square_one e x x.property)
  have hi (x : modelPlane e) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hs x
  refine {
    toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs
  }
  calc
    x * y = (x * y)⁻¹ := (hi (x * y)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hi, hi]

theorem centralProductModel_two_plane_cover :
    ∀ x : CentralProductModel, x ^ 2 = 1 → x ∈ modelPlane 0 ∨ x ∈ modelPlane 1 := by
  decide

/-- Transport the obstruction only along an actual group isomorphism. -/
theorem no_two_sixteen_cover_of_equiv (e : G ≃* CentralProductModel)
    (A B : Subgroup G) (hA : Nat.card A = 16) (hB : Nat.card B = 16) :
    ¬ (∀ x : G, orderOf x = 2 → x ∈ A ∨ x ∈ B) := by
  have hcount : Nat.card {x : G // x ^ 2 = 1} = 48 := by
    rw [← centralProductModel_square_one_card]
    apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro x
    change x ^ 2 = 1 ↔ e x ^ 2 = 1
    constructor
    · intro hx
      simpa only [map_pow, map_one] using congrArg e hx
    · intro hx
      apply e.injective
      simpa only [map_pow, map_one] using hx
  intro hcover
  have h := square_one_card_le_of_involution_cover A B hcover
  rw [hcount, hA, hB] at h
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
