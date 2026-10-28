module

public import Stellmacher.MainDefs
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.PGroup.NormalEightReduction
public import Stellmacher.Recognition.NormalEightCentralFour
public import Stellmacher.Recognition.NormalEightCentralInvolution

/-!
# Normal elementary eights in rank-three Sylow subgroups

Janko–Thompson's Main Theorem (Math. Z. 113 (1970), p.385) assumes
solvability of the centralizer of each Sylow involution t for which
[S : C_S(t)] ≤ 2. The N₂ condition implies the stronger assertion that
every involution centralizer is solvable: such a centralizer is itself
two-local. Neither simplicity nor a rank bound is needed for this step.

The two-group reduction imported here shows that a Sylow subgroup of
elementary rank at least three without a normal elementary eight must be
nonabelian, contain a normal four, and have central omega order two or four.
The imported central-four and central-involution arguments exclude both
cases in a finite nonsolvable simple N₂-group. Consequently every Sylow
subgroup containing an elementary subgroup of order at least eight also
contains a normal elementary subgroup of order at least eight. The proof
uses only the bound on normal elementary subgroups in its contradiction
hypothesis, with no rank bound on arbitrary elementary subgroups.

Source: `refs/original/n-group-global/odd-core-rank-two-source/
janko-thompson-1970-gdz.pdf`, Main Theorem p.385 and §6 pp.394–396.
-/

namespace Stellmacher

/-- N₂ implies solvability of every involution centralizer. -/
public theorem IsNTwoGroup.isSolvable_involution_centralizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    {t : G} (ht : orderOf t = 2) :
    Group.IsSolvable (Subgroup.centralizer ({t} : Set G)) :=
  hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer ht)

namespace Recognition

/-- The precise centralizer-solvability hypothesis in the Janko–Thompson
Main Theorem follows from N₂. The centralizer index is measured inside S. -/
public theorem jankoThompson_centralizer_hypothesis
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (t : S) (ht : orderOf t = 2)
    (_hindex : (Subgroup.centralizer ({t} : Set S)).index ≤ 2) :
    Group.IsSolvable (Subgroup.centralizer ({(t : G)} : Set G)) := by
  apply hN.isSolvable_involution_centralizer
  simpa only [Subgroup.orderOf_coe] using ht

/-- An ambient elementary subgroup contained in the Sylow gives the precise
two nonabelian normal-four cases when no normal elementary eight exists. -/
public theorem normal_eight_sylow_counterexample_cases
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ E : Subgroup S,
      E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    ¬ IsMulCommutative S ∧
      (Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2 ∨
        Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 4) ∧
      ∃ W : Subgroup S, W.Normal ∧ IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  let AS := A.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 AS := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 8 ≤ Nat.card AS := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv]
  exact S.isPGroup'.normal_four_cases_of_rank_three_of_no_normal_eight AS hAScard hno

/-- The rank-three consequence of Janko–Thompson: an elementary subgroup of
order at least eight in a Sylow two-subgroup of a finite nonsolvable simple
N₂-group forces a normal elementary subgroup of order at least eight. -/
public theorem exists_normal_elementary_eight_of_rank_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) :
    ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  by_contra hno
  obtain ⟨hnonab, hZ, W, hWn, hWe, hW⟩ :=
    S.isPGroup'.normal_four_cases_of_rank_three_of_no_normal_eight A hA hno
  let : W.Normal := hWn
  let : IsElementaryAbelian 2 W := hWe
  rcases hZ with htwo | hfour
  · exact NormalEightCentralInvolution.false_of_no_normal_eight
      hns hN S A hA hnonab htwo hno W hW
  · exact NormalEightCentralFour.false_of_normal_eight_central_four
      hns hN S A hA hnonab hfour hno W hW

/-- Ambient-subgroup form of the rank-three normal-eight theorem. -/
public theorem exists_normal_elementary_eight_of_le_sylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) :
    ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let AS := A.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 AS := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 8 ≤ Nat.card AS := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv]
  exact exists_normal_elementary_eight_of_rank_three hns hN S AS hAScard

end Recognition
end Stellmacher
