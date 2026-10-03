module

public import Theory.GroupTheory.ElementarySecondCenterSquares

/-!
# The square map over an elementary second-center subgroup

If D is elementary abelian, lies in the second center of K, and contains
all squares, then squaring induces a map K/D → D/(Z(K) ∩ D). The existing
representative-independence theorem supplies the quotient lift. Evaluation
and its zero criterion retain the actual group square.

Source: Parrott (1972), pp.673–674, the square-map construction.
-/

open Subgroup
namespace Subgroup
variable {K : Type*} [Group K] (D : Subgroup K) [D.Normal]
    [IsElementaryAbelian 2 D]

/-- Squaring on the literal quotient by an elementary subgroup of the second center. -/
public noncomputable def elementarySecondCenterSquare
    (hD : D ≤ upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D) :
    K ⧸ D → D ⧸ (center K).subgroupOf D :=
  Quotient.lift (fun x => QuotientGroup.mk' ((center K).subgroupOf D) ⟨x ^ 2, hsq x⟩) (by
    intro x y hxy
    apply QuotientGroup.eq.mpr
    change (x ^ 2)⁻¹ * y ^ 2 ∈ center K
    exact QuotientGroup.eq.mp
      (sq_eq_mod_center_of_eq_mod_elementary D hD x y (Quotient.sound hxy)))

public theorem elementarySecondCenterSquare_apply
    (hD : D ≤ upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D) (x : K) :
    elementarySecondCenterSquare D hD hsq (QuotientGroup.mk' D x) =
      QuotientGroup.mk' ((center K).subgroupOf D) ⟨x ^ 2, hsq x⟩ := by rfl

public theorem elementarySecondCenterSquare_one
    (hD : D ≤ upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D) :
    elementarySecondCenterSquare D hD hsq 1 = 1 := by
  change QuotientGroup.mk' ((center K).subgroupOf D) ⟨(1 : K) ^ 2, hsq 1⟩ = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change (1 : K) ^ 2 ∈ center K
  simp

public theorem elementarySecondCenterSquare_eq_one_iff
    (hD : D ≤ upperCentralSeries K 2) (hsq : ∀ x : K, x ^ 2 ∈ D) (x : K) :
    elementarySecondCenterSquare D hD hsq (QuotientGroup.mk' D x) = 1 ↔
      x ^ 2 ∈ center K := by
  rw [elementarySecondCenterSquare_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl
end Subgroup
