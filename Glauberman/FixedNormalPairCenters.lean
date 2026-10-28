module
public import Glauberman.FixedNormalPairRows

/-!
# Elementary centers of a numerical intersection pair

A maximum abelian subgroup contains the center. When that maximum subgroup
is elementary, every central element squares to one, identifying the full
embedded center with its central omega subgroup. The elementary maximum row
constructed by descent supplies this argument simultaneously for both pair
members and their intersection.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.6(b)–(e),
printedp46. The interval formulas for those centers are a subsequent step.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- An elementary maximum abelian subgroup forces the entire center to
have exponent two, so central omega is the full embedded center. -/
theorem omegaCenter_eq_center_of_elementary_maximum {S A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) [IsElementaryAbelian 2 A] :
    omegaCenterIn S = centerIn S := by
  have hzA : centerIn S ≤ A := le_maximum_abelian_of_centralizes hA inf_le_left
    (inf_le_right.trans (centralizer_le hA.1))
  ext x
  rw [mem_omegaCenterIn_iff]
  change (x ∈ S ∧ x ∈ centralizer (S : Set G) ∧ x ^ 2 = 1) ↔
    (x ∈ S ∧ x ∈ centralizer (S : Set G))
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,elemPow_eq_one_of_isElementaryAbelian x (hzA h)⟩⟩

/-- The original two centers and the center of their intersection are
already elementary. This uses the actual elementary maximum row furnished
by the numerical4.4/4.5 argument. -/
theorem NumericalPair.omegaCenters_eq_centers {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPair S T φ) :
    omegaCenterIn S = centerIn S ∧ omegaCenterIn T = centerIn T ∧
      omegaCenterIn (S ⊓ T) = centerIn (S ⊓ T) := by
  let P : IntersectionPair G := ⟨S,T,φ⟩
  obtain ⟨n,hE,hAS,hAT⟩ := P.exists_elementary_maximum_row h
  let A := (P.row n).left ⊓ (P.row n).right
  let _ : IsElementaryAbelian 2 A := hE
  have hAQ : A ∈ thompsonAbelianSubgroups (S ⊓ T) :=
    ⟨le_inf hAS.1 hAT.1,hAS.2.1,fun B hB hBc => hAS.2.2 B (hB.trans inf_le_left) hBc⟩
  exact ⟨omegaCenter_eq_center_of_elementary_maximum hAS,
    omegaCenter_eq_center_of_elementary_maximum hAT,
    omegaCenter_eq_center_of_elementary_maximum hAQ⟩
end Glauberman
