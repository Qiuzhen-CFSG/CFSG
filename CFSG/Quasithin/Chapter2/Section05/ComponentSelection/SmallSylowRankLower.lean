module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRanks
public import Theory.SpecificGroups.PSL3Two.FourNormalizers
public import Theory.GroupTheory.SemidihedralFourSubgroup
public import Theory.GroupTheory.PrimeRankElementary
/-!
# Rank-two witnesses in the original small-component Sylow groups

The dihedral and semidihedral presentations supply an actual four subgroup.
Its elementary order gives the lower two-rank bound used to upgrade the
invariant two-component in source 2.5.19 to an ordinary component.
Source: Aschbacher–Smith 2.5.8(3), printed p.556, and 2.5.19, pp.560–561.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
theorem SourceSylowTwoShape.exists_four_le {K : Type*} [Group K] [Finite K]
    (P : Sylow 2 K) (h : SourceSylowTwoShape P) :
    ∃ F : Subgroup K, F ≤ P ∧ IsKleinFour F := by
  unfold SourceSylowTwoShape at h
  rcases h with h | h
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    exact GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (P : Subgroup K) (by omega) e
  · obtain ⟨e⟩ := h
    let a := e.symm (Semidihedral.standardRotation 4 (by omega))
    let b := e.symm (Semidihedral.standardReflection 4 (by omega))
    have ha : orderOf a = 8 := (e.symm.orderOf_eq _).trans (Semidihedral.standardRotation_order 4 (by omega))
    have hb : orderOf b = 2 := (e.symm.orderOf_eq _).trans (Semidihedral.standardReflection_order 4 (by omega))
    have hab : b * a * b⁻¹ = a ^ 3 := by
      have hh := congrArg e.symm (Semidihedral.standard_conjugation 4 (by omega))
      norm_num only [map_mul, map_inv, map_pow] at hh
      exact hh
    have hgen : closure ({a, b} : Set P) = ⊤ := by
      have hh := congrArg (Subgroup.map e.symm.toMonoidHom)
        (Semidihedral.standard_generators 4 (by omega))
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
        map_top_of_surjective _ e.symm.surjective] at hh
      exact hh
    obtain ⟨F, hF, hc, hFP⟩ := Semidihedral.exists_four_le (P : Subgroup K)
      (by omega : 4 ≤ 4) a b ha hb hab hgen
    let := hF
    let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact ⟨F, hFP, ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩⟩


/-- Every original small-component Sylow shape forces two-rank at least two. -/
theorem SourceSylowTwoShape.two_le_rank {K:Type*} [Group K] [Finite K]
    (P:Sylow 2 K) (h:SourceSylowTwoShape P) : 2≤primeRank 2 K := by
  obtain ⟨F,_,hF⟩:=h.exists_four_le P
  let :=hF
  let : IsElementaryAbelian 2 F := { toIsMulCommutative := IsKleinFour.isMulCommutative, exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  exact IsElementaryAbelian.primeRank_ge_of_card F (by simp [IsKleinFour.card_four])
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
