module
public import Theory.SpecificGroups.SL2.SylowOvergroupComponentUnique
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# Unique C-components in symplectic rank-two Sylow overgroups

Proper Sylow overgroups lie in point or plane parabolics. Each parabolic's
solvable residual has a two-core quotient equal to the actual SL₂(F).
Solvable extensions and restriction to the original full Sylow therefore
prove uniqueness, without inferring it from a generalized-Fitting bound.
Source: Aschbacher--Smith A.3.12, pp.47--48; 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
theorem pointParabolic_sylow_component_unique {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) :
    SylowOvergroupComponentUnique (pointParabolic (F := F)) := by
  apply SylowOvergroupComponentUnique.of_residual_image _ _
    (pointParabolic_solvableResidual_eq hF hn)
  let : Group.IsNilpotent (pCore 2 (pointLocal (F := F))) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (pointLocal (F := F)))
  exact SylowOvergroupComponentUnique.of_equiv (pointLocalCoreQuotientEquiv hF hn)
    (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F)

theorem planeParabolic_sylow_component_unique {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) :
    SylowOvergroupComponentUnique (planeParabolic (F := F)) := by
  apply SylowOvergroupComponentUnique.of_residual_image _ _
    (planeParabolic_solvableResidual_eq hF hn)
  let : Group.IsNilpotent (pCore 2 (planeLocal (F := F))) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (planeLocal (F := F)))
  exact SylowOvergroupComponentUnique.of_equiv (planeLocalCoreQuotientEquiv hF hn)
    (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F)

theorem sylow_overgroup_component_unique [IsSimpleGroup (Sp F)] [Group.IsPerfect (Sp F)]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) : SylowOvergroupComponentUnique (Sp F) := by
  apply SylowOvergroupComponentUnique.of_proper_conjugate_cover
  intro S P hSP hP
  have htwo : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover htwo S P hSP hP
  rcases hg with hg | hg
  · exact ⟨g,pointParabolic,hg,pointParabolic_sylow_component_unique F hF hn⟩
  · exact ⟨g,planeParabolic,hg,planeParabolic_sylow_component_unique F hF hn⟩
end Theory.SpecificGroups.SymplecticFour

