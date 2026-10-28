module

public import CFSG.Quasithin.ChapterK.Defs
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.SubspaceCodimensionLoss

/-!
# Numerical reductions for the Chapter K families

The minimum involution codimension bounds every elementary actor's fixed
codimension. This proves (*) on p.452 and the noncyclic-actor reduction (**)
on p.458, using actual actors attaining the quadratic or cubic infimum.
The hyperplane inequality also supplies the final linear step of the M₁₂
argument: ambient fixed codimension six leaves at least five on its invariant
hyperplane, excluding a rank-two actor of ratio at most two.

These reductions do not classify modules or supply their local group geometry.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), Chapter K,
printed pp.452 and 458–460.
-/

public section
namespace CFSG.Quasithin.ChapterK
open Representation Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Equation (*) in the introduction: an actor of ratio below m is noncyclic. -/
theorem one_lt_rank_of_actionRatio_lt_moduleM {A : Subgroup G}
    (hA : IsElementaryTwo A) (hr : actionRatio ρ A < (ChapterE.moduleM ρ : ℝ≥0∞)) :
    1 < rank A := by
  have hpos := hA.rank_pos
  by_contra! hle
  have hone : rank A = 1 := by omega
  have hcodim := ChapterE.moduleM_le_fixedCodim ρ hA
  have hcodim' : (ChapterE.moduleM ρ : ℝ≥0∞) ≤ fixedCodim ρ A := by
    exact_mod_cast hcodim
  rw [actionRatio, hone, Nat.cast_one, div_one] at hr
  exact not_lt_of_ge hcodim' hr

omit [Finite G] in
/-- The first reduction in K.4: every actor satisfying (**) is noncyclic. -/
theorem one_lt_rank_of_small_ratio {A : Subgroup G} (hA : IsElementaryTwo A)
    (hm : 2 < ChapterE.moduleM ρ) (hr : fixedCodim ρ A ≤ 2 * rank A) :
    1 < rank A := by
  have hcodim := ChapterE.moduleM_le_fixedCodim ρ hA
  omega

/-- A small quadratic ratio gives an actual member of D(G,V), under m > 2. -/
theorem exists_quadraticSubgroup_of_ratio_le_two
    (hm : 2 < ChapterE.moduleM ρ) (hq : quadraticRatio ρ ≤ 2) :
    ∃ A ∈ quadraticSubgroups ρ, fixedCodim ρ A ≤ 2 * rank A := by
  obtain ⟨A, hA, hquad, hr⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  exact ⟨A, ⟨hA, one_lt_rank_of_small_ratio ρ hA hm hr, hquad⟩, hr⟩

/-- The J₂ branch uses a cubic actor in (**), without asserting quadraticity. -/
theorem exists_noncyclic_cubic_of_ratio_le_two
    (hm : 2 < ChapterE.moduleM ρ) (hq : cubicRatio ρ ≤ 2) :
    ∃ A, IsElementaryTwo A ∧ 1 < rank A ∧ IsCubic ρ A ∧
      fixedCodim ρ A ≤ 2 * rank A := by
  obtain ⟨A, hA, hc, hr⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  exact ⟨A, hA, one_lt_rank_of_small_ratio ρ hA hm hr, hc, hr⟩

/-- Excluding all small actors in D(G,V) proves the strict quadratic bound. -/
theorem two_lt_quadraticRatio_of_quadraticSubgroups
    (hm : 2 < ChapterE.moduleM ρ)
    (hD : ∀ A ∈ quadraticSubgroups ρ, 2 * rank A < fixedCodim ρ A) :
    2 < quadraticRatio ρ := by
  by_contra! hq
  obtain ⟨A, hA, hr⟩ := exists_quadraticSubgroup_of_ratio_le_two ρ hm hq
  exact (not_lt_of_ge hr) (hD A hA)

omit [Finite G] in
/-- The literal invariant-hyperplane calculation in the terminal M₁₂ argument.
The rank and ambient fixed codimension come from its separate local geometry. -/
theorem hyperplane_rank_two_exclusion (W : Subrepresentation ρ) (A : Subgroup G)
    (hW : Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) = 1)
    (hA : rank A = 2) (hambient : 6 ≤ fixedCodim ρ A) :
    2 * rank A < fixedCodim W.toRepresentation A := by
  have h := fixedCodim_le_subrepresentation_add_codim ρ W A
  omega

end CFSG.Quasithin.ChapterK
