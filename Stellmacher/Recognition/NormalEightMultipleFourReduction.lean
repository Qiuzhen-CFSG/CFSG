module

public import Theory.GroupTheory.PGroup.NormalEightDihedralCentralizer
public import Theory.GroupTheory.PGroup.DihedralCentralFactorSylow
public import Theory.GroupTheory.PGroup.DihedralCyclicCentralFactorSylow
public import Theory.GroupTheory.PGroup.DihedralQuaternionCentralFactorSylow
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Multiple normal fours without a normal elementary eight

Distinct normal elementary fours generate a dihedral central factor. Its
centralizer has no normal four and is therefore cyclic, generalized quaternion,
dihedral, or semidihedral. The cyclic case collapses the Sylow subgroup to the
dihedral eight by transfer. The quaternion case gives a weakly closed
involution, contradicting the proved simple-group Z-star consequence.

For a Sylow containing an elementary subgroup of order at least eight, the
cyclic case is also impossible. The last theorem records exactly the two
remaining centralizer alternatives, without imposing an elementary rank bound.
Their ambient exclusions and final assembly are re-exported by
`NormalEightMultipleFour`. Source: Janko–Thompson (1970), result 1.2,
printed pp.385–386, used on p.394.
-/

namespace Stellmacher.Recognition.NormalEightMultipleFour

open Subgroup

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The quaternion centralizer case is impossible by weak closure and Z-star;
no elementary rank bound or N₂ hypothesis is needed. -/
public theorem false_of_quaternion_centralizer
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    (m : ℕ) (hm : 0 < m)
    (f : centralizer (D : Set S) ≃* QuaternionGroup m) : False := by
  obtain ⟨z, hz, -, hweak⟩ :=
    S.exists_weakly_closed_involution_of_dihedral_quaternion_factor D e hgen m hm f
  obtain ⟨t, hne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  exact hne (hweak t hconj)

/-- A dihedral eight cannot fill a group containing an elementary eight and
having no normal elementary eight. -/
public theorem dihedral_factor_ne_top_of_elementary_eight
    {P : Type*} [Group P] [Finite P]
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4) : D ≠ ⊤ := by
  intro htop
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hP : Nat.card P = 8 := by
    simpa only [htop, Nat.card_congr Subgroup.topEquiv.toEquiv] using hD
  have hAtop : A = ⊤ := A.eq_top_of_card_eq
    (le_antisymm A.card_le_card_group (by omega))
  have hAn : A.Normal := hAtop ▸ inferInstanceAs (⊤ : Subgroup P).Normal
  exact hno ⟨A, hAn, inferInstance, hA⟩

/-- Transfer excludes the cyclic-centralizer branch under the actual
no-normal-eight hypotheses. -/
public theorem false_of_cyclic_centralizer
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (D : Subgroup S) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set S) = ⊤)
    [IsCyclic (centralizer (D : Set S))] : False := by
  apply dihedral_factor_ne_top_of_elementary_eight A hA hno D e
  exact S.dihedral_factor_eq_top_of_cyclic_centralizer_of_no_normal_index_two
    (S.no_normal_index_two_of_dihedral_subgroup D e) D e hgen

/-- Under no-normal-eight, the only unexcluded centralizers of the dihedral
join are dihedral and semidihedral. All cardinalities refer to the actual
centralizer inside the given Sylow subgroup. -/
public theorem dihedral_or_semidihedral_centralizer_of_distinct_normal_fours
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W F : Subgroup S) [W.Normal] [F.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 F]
    (hW : Nat.card W = 4) (hF : Nat.card F = 4) (hne : F ≠ W) :
    (∃ m : ℕ, Nonempty (centralizer ((W ⊔ F : Subgroup S) : Set S) ≃* DihedralGroup m)) ∨
    (∃ n : ℕ, 4 ≤ n ∧
      Nat.card (centralizer ((W ⊔ F : Subgroup S) : Set S)) = 2 ^ n ∧
      ∃ a b : centralizer ((W ⊔ F : Subgroup S) : Set S),
        orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧ closure ({a, b} : Set _) = ⊤) := by
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours_of_no_normal_eight
    hno W F hW hF hne.symm
  have hgen := sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
    S.isPGroup' hno W F hW hF hne.symm
  have hcases := centralizer_isBinaryHallFactor_of_distinct_normal_fours_of_no_normal_eight
    S.isPGroup' hno W F hW hF hne.symm
  rcases hcases with hcyc | hquat | hdih | hsemi
  · let : IsCyclic (centralizer ((W ⊔ F : Subgroup S) : Set S)) := hcyc
    exact (false_of_cyclic_centralizer S A hA hno (W ⊔ F) e hgen).elim
  · obtain ⟨n, -, ⟨f⟩⟩ := hquat
    exact (false_of_quaternion_centralizer hns S (W ⊔ F) e hgen
      (2 ^ (n - 2)) (by positivity) f).elim
  · exact Or.inl hdih
  · exact Or.inr hsemi

end Stellmacher.Recognition.NormalEightMultipleFour
