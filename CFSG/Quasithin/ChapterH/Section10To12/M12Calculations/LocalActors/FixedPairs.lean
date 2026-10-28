module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Outer
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs.LinearAction
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs.SubgroupPlacement

/-!
# The inner/outer fixed pair for H.11.1(4)

Every elementary sixteen contains an outer involution t and an inner involution
z in the actual A₅ factor of its inner centralizer. That factor provides an
order-five commutator [z,g]. The kernel on C_V(t) has exponent two, so this
commutator acts nontrivially there and moves at least four dimensions. Hence z
moves at least two of the five dimensions of C_V(t), giving the required common
fixed-space bound three.

The only additional inputs are the authorized native inner two-rank bound,
outer involution fusion, and outer fixed-subgroup table row. The parent H.11
assembly owns their discharge. Subgroup placement and the restricted action
calculation are proved here. The resulting pair feeds
`LocalActors.dimensions_of_inner_outer_fixed_pair` for both source dimension
bounds. No inner C₂ × S₅ row or additional module bound is needed.

Source: Aschbacher–Smith H.11.1(4), printed pp.392–393, combined manuscript of
1 March 2004.
-/

public section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- An actual inner/outer pair in each elementary sixteen, with common fixed
space of dimension at most three. The model table premises remain explicit. -/
theorem exists_inner_outer_fixed_pair (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)
    (hinner : primeRank 2 M12 ≤ 3) (hfusion : OuterInvolutionFusion)
    (htable : FixedPairs.OuterFixedSubgroupTable)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ t z : G, t ∈ A ∧ t ∉ solvableResidual G ∧ orderOf t = 2 ∧
      z ∈ A ∧ z ∈ solvableResidual G ∧ orderOf z = 2 ∧
      Module.finrank (ZMod 2)
        (fixedSpace ρ (zpowers t) ⊓ fixedSpace ρ (zpowers z) : Submodule (ZMod 2) V) ≤ 3 := by
  obtain ⟨t, z, g, htA, htL, ht, hzA, hzL, hz, _, htz, htg, hcomm⟩ :=
    FixedPairs.exists_centralizing_commutator_five d hinner htable A hA hcard
  let zc : centralizer ({t} : Set G) := ⟨z, mem_centralizer_singleton_iff.mpr htz.symm⟩
  let gc : centralizer ({t} : Set G) := ⟨g, mem_centralizer_singleton_iff.mpr htg.symm⟩
  have hc : orderOf (zc * gc * zc⁻¹ * gc⁻¹) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hcomm
  refine ⟨t, z, htA, htL, ht, hzA, hzL, hz, ?_⟩
  exact FixedPairs.common_fixed_finrank_le_three ρ h.faithful
    (ht ▸ pow_orderOf_eq_one t) zc gc hc
    (finrank_fixedSpace_outer_involution ρ h d hfusion htL ht)

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
