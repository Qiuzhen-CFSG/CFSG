module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Stellmacher.Recognition.NormalEightCentralFourNontrivialNormalizer
public import Stellmacher.Recognition.NormalEightCentralFourTrivialNormalizer

/-!+# Reductions for the central-four normal-eight branch

For a Sylow two-subgroup with central omega of order four, an elementary
subgroup of rank three contradicts centrality of every involution. Under
the no-normal-eight hypothesis every normal elementary four is central,
so fusion of two distinct elements in such a four contradicts the trivial
Sylow-normalizer action.

These reductions isolate the two ambient inputs in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1, pp.386 and 393–394:
the nontrivial-normalizer branch must prove centrality of all involutions;
the trivial-normalizer branch must produce fusion in the central four.
The latter requires the full p.394 argument beyond the elementary sixteen.
The source is saved as
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightCentralFour

open Subgroup

/-- Centrality of all Sylow involutions excludes elementary rank three
when the central omega has order four. -/
public theorem false_of_involutions_central
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hcentral : ∀ x : S, orderOf x = 2 → x ∈ center S) : False := by
  obtain ⟨x, hx, hxc⟩ :=
    exists_noncentral_involution_of_rank_three_of_omega_center_four A hA hZ
  exact hxc (hcentral x hx)

/-- Fusion of distinct elements in a normal elementary four excludes
the trivial Sylow-normalizer action under the no-normal-eight hypothesis. -/
public theorem normalizer_ne_of_distinct_fused_normal_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (z t : S) (hz : z ∈ W) (ht : t ∈ W) (hne : z ≠ t)
    (hconj : IsConj (z : G) (t : G)) :
    normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G) := by
  have hWc : W ≤ center S :=
    (normal_elementary_le_omega_center_of_no_normal_eight hno hZ W).trans
      (map_subtype_le _)
  intro hN
  exact hne (S.eq_of_isConj_of_mem_center_of_normalizer_eq hN z t (hWc hz) (hWc ht) hconj)

/-- A rank-three elementary subgroup is impossible when the central omega
four is the central-four case of the normal-eight reduction. The two possible
Sylow-normalizer actions are discharged by the corresponding ambient
recognition branches. -/
public theorem false_of_normal_eight_central_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN2 : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) : False := by
  by_cases hnorm : normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ centralizer (S : Set G)
  · exact false_of_involutions_central S A hA hZ
      (involutions_central_of_normalizer_ne hns hN2 S hnonab hZ hno W hW hnorm)
  · apply false_of_normalizer_eq hns hN2 S hnonab hZ hno W hW
    by_contra hEq
    exact hnorm hEq

end Stellmacher.Recognition.NormalEightCentralFour
