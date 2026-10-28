module

public import Stellmacher.Recognition.NormalEightMultipleFourReduction
public import Theory.GroupTheory.PGroup.DihedralSquareCentralFactor
public import Theory.GroupTheory.SemidihedralSquareData

/-!
# Excluding the semidihedral centralizer of two normal fours

A Sylow two-subgroup of a finite nonsolvable simple group cannot be generated
by a dihedral-eight subgroup and its semidihedral centralizer. The explicit
semidihedral presentation gives a center of order two, central squares of
fourth roots, and a normal cyclic four. The dihedral factor then supplies
commuting fourth roots for every involution, making the common central
involution weakly closed. The simple-group Z-star consequence contradicts this.

In particular, this excludes the semidihedral branch of
`NormalEightMultipleFour.dihedral_or_semidihedral_centralizer_of_distinct_normal_fours`.
No bound on elementary rank or local-solvability hypothesis is needed.

Source: the central-product reduction toward Janko–Thompson, Math. Z. 113
(1970), result 1.2, printed pp.385–386. The semidihedral calculations are those
of Alperin–Brauer–Gorenstein, Chapter II, Section 1, Lemma 1, printed p.9.
-/

namespace Stellmacher.Recognition.NormalEightMultipleFour

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- A dihedral-eight central factor with explicitly semidihedral centralizer
contradicts simple-group involution fusion. -/
public theorem false_of_semidihedral_centralizer
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    (n : ℕ) (hn : 4 ≤ n) (a b : centralizer (D : Set S))
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hCgen : closure ({a, b} : Set _) = ⊤) : False := by
  obtain ⟨hcenter, hsquare, q, hq, hqconj⟩ :=
    Semidihedral.square_data hn a b ha hb hconj hCgen
  obtain ⟨z, hz, -, hweak⟩ :=
    S.exists_weakly_closed_involution_of_dihedral_square_factor
      D e hgen hcenter hsquare q hq hqconj
  obtain ⟨t, hne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact hne (hweak t hconj)

/-- The semidihedral alternative for the centralizer of the join of distinct
normal fours is impossible under the actual no-normal-eight hypothesis. -/
public theorem false_of_semidihedral_centralizer_of_distinct_normal_fours
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W F : Subgroup S) [W.Normal] [F.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 F]
    (hW : Nat.card W = 4) (hF : Nat.card F = 4) (hne : F ≠ W)
    (hsd : ∃ n : ℕ, 4 ≤ n ∧
      Nat.card (centralizer ((W ⊔ F : Subgroup S) : Set S)) = 2 ^ n ∧
      ∃ a b : centralizer ((W ⊔ F : Subgroup S) : Set S),
        orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧ closure ({a, b} : Set _) = ⊤) :
    False := by
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours_of_no_normal_eight
    hno W F hW hF hne.symm
  have hgen := sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
    S.isPGroup' hno W F hW hF hne.symm
  obtain ⟨n, hn, -, a, b, ha, hb, hconj, hCgen⟩ := hsd
  exact false_of_semidihedral_centralizer hns S (W ⊔ F) e hgen n hn a b ha hb hconj hCgen

end Stellmacher.Recognition.NormalEightMultipleFour
