module
public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Mathlib.GroupTheory.Sylow

/-!
# The unique line centralized by a Sylow subgroup with center of order two

Any subgroup of order two centralized by a full Sylow two-subgroup lies
in that Sylow subgroup by maximality, and hence is its entire center.
This compares literal involution centralizers without changing the Sylow.

Source application: Aschbacher--Smith 5.1.13, printed p.637,
refs/quasithin.pdf, the common-container argument in the J₄ row.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]
/-- Every order-two subgroup centralized by S is its center image. -/
theorem eq_center_image_of_card_two (S : Sylow 2 G) (hZ : Nat.card (center S) = 2)
    (A : Subgroup G) (hA : Nat.card A = 2)
    (hS : (S : Subgroup G) ≤ centralizer (A : Set G)) :
    A = (center S).map (S : Subgroup G).subtype := by
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hAS : A ≤ (S : Subgroup G) := by
    have he := S.is_maximal' (hAp.to_sup_of_normal_left' S.isPGroup'
      (hS.trans (centralizer_le_normalizer _))) le_sup_right
    exact he ▸ le_sup_left
  apply eq_of_le_of_card_ge
  · rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf hAS (le_centralizer_iff.mp hS)
  · rw [card_map_of_injective (S : Subgroup G).subtype_injective, hZ, hA]
end Sylow
