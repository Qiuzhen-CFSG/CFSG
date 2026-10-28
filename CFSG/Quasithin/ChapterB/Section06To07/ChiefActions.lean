module
public import Theory.Representation.BinaryOffender.IrreducibleResidual
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman

/-!
# Genuine chief-action inputs for a minimal parabolic

A nontrivial irreducible binary action detects the two-residual. Its kernel
therefore lies in the maximal-overgroup core, whose intersection with the
specified Sylow group is O₂(H). Conversely O₂(H) acts trivially, giving the
exact relative kernel on every subgroup of that Sylow group. If H is solvable,
B.1.8 excludes ratios below one on the literal faithful action image.
Source: Aschbacher–Smith B.6.8(6) and D.1.2(5)/D.1.3, pp.114,173.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterB
variable {H W : Type*} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
theorem solvable_irreducible_image_ratio_ge_one
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hs : Group.IsSolvable H) : 1 ≤ quadraticRatio (imageRepresentation ρ) := by
  let : Group.IsSolvable H := hs
  have hsol : Group.IsSolvable (actionImage ρ) :=
    Group.isSolvable_of_surjective ρ.asGroupHom.rangeRestrict_surjective
  by_cases hf : IsFFModule (imageRepresentation ρ)
  · exact (Glauberman.numerical_conclusions hsol (irreducible_image_twoCore_eq_bot ρ)
      (imageRepresentation_injective ρ) hf).1.ge
  · exact (lt_of_not_ge (fun h => hf ((isFFModule_iff_quadraticRatio_le_one _).mpr h))).le

theorem minimalParabolic_irreducible_sylow_kernel
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hn : ∃ h w, ρ h w ≠ w) (A : Subgroup H) (hAT : A ≤ T) :
    A ⊓ ρ.ker = A ⊓ pCore 2 H := by
  have hk : ρ.ker ≤ minimalParabolicCore T hP :=
    minimalParabolic_source6a T hP ρ (irreducible_residual_not_le_ker ρ hn)
  have hc : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  apply le_antisymm
  · apply le_inf inf_le_left
    rw [← minimalParabolic_sylow_inf_core T hP]
    exact le_inf (inf_le_left.trans hAT) (inf_le_right.trans hk)
  · exact inf_le_inf_left _ hc
end CFSG.Quasithin.ChapterB
