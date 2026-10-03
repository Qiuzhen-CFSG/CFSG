module

public import Stellmacher.Recognition.Catalogue
public import Stellmacher.Recognition.SimpleReduction
public import Stellmacher.Recognition.Sp4TwoExclusion
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# Recognized models and the remaining simple N2 alternatives

The proved Bender--Suzuki and Gorenstein--Walter branches now lie in the
actual N2 catalogue. Nonsolvability excludes the three-element field in
the odd PSL2 branch. The local Sp4(2) configuration is impossible by the
square-plane transfer theorem. The two remaining exceptional local types,
semidihedral Sylow subgroups, the order-32 maximal-local configuration,
and a nontrivial involution-centralizer odd core are explicit alternatives.

This sharpens the proved simple N2 reduction from Stellmacher's Theorem 2.
It does not assert the missing global recognition of those alternatives.
Sources and model parameters are documented in the imported catalogue and
recognition modules.
-/

namespace Stellmacher.Recognition
universe u

public theorem isNTwoGroupModel_of_bender {G : Type u} [Group G]
    (h : IsSimpleBenderGroup G) : IsNTwoGroupModel G := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl (.psl2Even n hn e)
  · exact Or.inl (.suzuki n hn e)
  · exact Or.inr ⟨n, hn, ⟨e⟩⟩

public theorem isNTwoGroupModel_of_odd_psl2 {G : Type u} [Group G]
    (hns : ¬ Group.IsSolvable G)
    (K : Type u) [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (e : G ≃* GorensteinWalter.PSL2 K) : IsNTwoGroupModel G := by
  have hKns : ¬ Group.IsSolvable (GorensteinWalter.PSL2 K) := by
    intro hK
    let _ := hK
    exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  exact Or.inl (.psl2Odd K hodd
    (Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable hodd hKns) e)

/-- Actual recognized models, or one of the remaining global N2 cases. -/
public theorem simple_nTwo_catalogue_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S0 : Sylow 2 G) :
    IsNTwoGroupModel G ∨
    (IsOfGTwoTwoDerivedType G ∨ IsOfTwistedF4TwoDerivedType G) ∨
    IsSemidihedralGroup S0 ∨
    (Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup G, IsMaximalTwoLocal U ∧
      Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  rcases simple_nTwo_recognition_reduction hns hN S0 with
    hB | hGW | htype | hsd | h32 | hodd
  · exact Or.inl (isNTwoGroupModel_of_bender hB)
  · rcases hGW with hA | hPSL
    · obtain ⟨e⟩ := hA
      exact Or.inl (Or.inl (.alternatingSeven e))
    · obtain ⟨K, hK, hfin, hodd, ⟨e⟩⟩ := hPSL
      let _ := hK
      let _ := hfin
      exact Or.inl (isNTwoGroupModel_of_odd_psl2 hns K hodd e)
  · rcases htype with hsp4 | hrest
    · exact (not_sp4Two_type_of_simple_nonsolvable hns hsp4).elim
    · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inl hsd))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h32)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hodd)))

end Stellmacher.Recognition
