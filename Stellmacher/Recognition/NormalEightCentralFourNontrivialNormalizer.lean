module

public import Theory.GroupTheory.InvolutionCounting
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Stellmacher.MainDefs
public import Stellmacher.Recognition.NormalEightMacWilliamsAlternatives

/-!
# Assembly of the nontrivial-normalizer central-four branch

The numerical consequence needed from the MacWilliams alternatives is a
bound of three on the number of Sylow involutions, unless an ambient
involution has nonsolvable centralizer. The latter alternative is excluded
by the N₂ hypothesis. Counting against the central omega four then proves
centrality of every Sylow involution.

The recognition dichotomy itself remains an input here. It is the substantial
content of Janko–Thompson, Math. Z. 113 (1970), Theorems 1.3 and 1.5, p.386,
used in the first paragraph of Lemma 5.1, p.393. Source:
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
In particular no rank bound or three-involution hypothesis is inferred just
from the absence of a normal elementary eight.
-/

namespace Stellmacher.Recognition.NormalEightCentralFour

open Subgroup

/-- Discharge the numerical and centralizer alternatives of the recognition
step. The construction of these alternatives is a separate obligation. -/
public theorem involutions_central_of_macwilliams_alternatives
    {G : Type*} [Group G] [Finite G]
    (hN2 : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hcases : Nat.card {x : S // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  rcases hcases with hcount | ⟨z, hz, hns⟩
  · exact involutions_central_of_card_le_three_of_omega_center_four hZ hcount
  · exact False.elim (hns (hN2 _ (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)))

/-- In the nontrivial Sylow-normalizer branch, every Sylow involution is
central. MacWilliams' alternatives give either the three-involution count or
a nonsolvable involution centralizer; the latter contradicts the N₂
hypothesis. -/
public theorem involutions_central_of_normalizer_ne
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN2 : IsNTwoGroup G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  exact involutions_central_of_macwilliams_alternatives hN2 S hZ
    (NormalEightCentralFour.macwilliams_alternatives_of_normalizer_ne
      hns S hnonab hZ hno W hW hnorm)

end Stellmacher.Recognition.NormalEightCentralFour
