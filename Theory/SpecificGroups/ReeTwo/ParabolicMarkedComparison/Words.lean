module

public import Theory.SpecificGroups.ReeTwo.Relations
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics

/-!
# The marked Ree-two roots in the ambient binary Ree group

Shinoda's roots 1, 3, 4, 5, 6, 7, 9 and 10 are respectively Parrott's
relative-root words u1, u8, u7, u5, u3, u2, u6 and u4. Roots 8, 11 and 12
are the squares of roots 4, 6 and 5. The orientation here is the orientation
of the already verified Parrott realization. These are actual exceptional
fixed matrices, and every positive word belongs to the specified ambient
Sylow subgroup. The Weyl element is the actual first parabolic reflection.

`Relations` asks only for the finite root and complement identities needed
by `Centralizer.lift`; it assumes no subgroup structure or isomorphism.
Their verification is separate from these unconditional definitions.

Sources: Shinoda (1975), pp.80–82, (2.1)–(2.3) and the Weyl table;
Parrott (1972), §5, p.683; Aschbacher–Smith, 14.2.21, printed p.989.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.Binary.FixedGeometry
namespace Ambient

/-- The eight oriented relative root elements in the actual fixed group. -/
def relative (i : Fin 8) : Model 0 := ⟨u i, (mem_fixedSubgroup 0 _).mpr (u_fixed i)⟩

/-- Source root 1. Its square is source root 2. -/
def rootOne : Model 0 := relative 0

/-- Source roots 3 through 12, indexed as in `ReeTwo.Core`. -/
def root : CoreRoot → Model 0 :=
  ![relative 7, relative 6, relative 4, relative 2, relative 1,
    relative 6 ^ 2, relative 5, relative 3, relative 2 ^ 2, relative 4 ^ 2]

/-- The actual Suzuki-side Weyl lift. -/
def weyl : Model 0 := weylLift 0 .suzuki

private theorem pair_mem_positive (i : Fin 4) : pairElement i ∈ splitUnipotent 0 := by
  rw [pairElement_eq]
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inl (i, 0))).property, rfl⟩
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inl (i, 1))).property, rfl⟩

private theorem quartet_mem_positive (i : Fin 4) :
    quartetElement i ∈ splitUnipotent 0 := by
  rw [quartetElement_eq]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.subset_closure ⟨_, 1,
        ((rootBlocks .positive).roots (.inr (i, 0))).property, rfl⟩
    · exact Subgroup.subset_closure ⟨_, 1,
        ((rootBlocks .positive).roots (.inr (i, 1))).property, rfl⟩
  · exact Subgroup.subset_closure ⟨_, 1,
      ((rootBlocks .positive).roots (.inr (i, 3))).property, rfl⟩

theorem relative_mem_sylow (i : Fin 8) :
    relative i ∈ Tits.ExceptionalParabolics.FullRee.S := by
  change toSplitGroup 0 (relative i) ∈ splitUnipotent 0
  rw [toSplitGroup_apply]
  change u i ∈ splitUnipotent 0
  fin_cases i <;> simp [u, pair_mem_positive, quartet_mem_positive]

theorem root_mem_sylow (i : CoreRoot) :
    root i ∈ Tits.ExceptionalParabolics.FullRee.S := by
  fin_cases i <;> simp only [root]
  all_goals first
    | exact relative_mem_sylow _
    | exact Subgroup.pow_mem _ (relative_mem_sylow _) _

theorem rootOne_mem_sylow : rootOne ∈ Tits.ExceptionalParabolics.FullRee.S :=
  relative_mem_sylow 0

theorem weyl_mem_first : weyl ∈ Tits.ExceptionalParabolics.FullRee.first :=
  weylLift_mem_seed 0 .suzuki

/-- Parrott's local generators written in the source-root marking. -/
def parrottWord : Tits.ParrottGenerator → Model 0
  | .r1 => weyl
  | .r8 => weylLift 0 .linear
  | .s1 => rootOne * rootOne
  | .s2 => root 4
  | .s3 => rootOne * root 3
  | .s4 => root 7
  | .s5 => rootOne * root 2
  | .s6 => root 6
  | .s7 => root 1 * rootOne⁻¹
  | .s8 => root 0

/-- These words are literally the marked Atlas embedding, not a choice by order. -/
theorem atlas_generator (i : Tits.ParrottGenerator) :
    Tits.ExceptionalParabolics.FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment i) =
      parrottWord i := by
  apply toSplitGroup_injective 0
  rw [Tits.ExceptionalParabolics.FullRee.atlasEmbedding_generator_matrix]
  cases i with
  | r1 => exact (toSplitGroup_weylLift 0 .suzuki).symm
  | r8 => exact (toSplitGroup_weylLift 0 .linear).symm
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 =>
    simp [parrottWord, rootOne, root, relative, assignment]

/-- Exactly the relation hypotheses of the universal coordinate map. -/
structure Relations : Prop where
  core : CoreRelations root
  root_one : RootOneRelations rootOne root
  weyl_root (i : CoreRoot) : weyl * root i * weyl⁻¹ = root (weylRoot i)
  five : ((rootOne⁻¹) ^ 2 * weyl) ^ 5 = 1
  four : (rootOne⁻¹) ^ 4 = 1
  action : rootOne⁻¹ * ((rootOne⁻¹) ^ 2 * weyl) * (rootOne⁻¹)⁻¹ =
    ((rootOne⁻¹) ^ 2 * weyl) ^ 2

end Ambient
end ReeTwo.ParabolicMarkedComparison
