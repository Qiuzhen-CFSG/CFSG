module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Proper local components in special linear dimension three

Project to PSL₃, use its full-Sylow local-component placement, and lift the
point or line residual through the actual central projection. Perfectness
removes the central kernel in both directions. No marking of the smaller
two-core quotient and no condition on the size of the center is required.

Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48 and 751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every proper full-Sylow local C-component is a conjugate parabolic residual. -/
theorem special_linear_three_local_placement {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ g : SL(3,F),
      B.map (MulAut.conj g).toMonoidHom = pointLocalSL F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocalSL F := by
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup SL(3,F)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hker : (projection F).ker ≤ center SL(3,F) := (projection_ker F).le
  have hp : B.map (projection F) ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect (projection F) hker ⊤ B
    rw [ht]
    exact le_top
  obtain ⟨g,hg⟩ := linear_three_local_placement hF hn
    (S.mapSurjective (projection_surjective F)) (B.map (projection F))
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB (projection F)) hp
  obtain ⟨g,rfl⟩ := projection_surjective F g
  let A := B.map (MulAut.conj g).toMonoidHom
  let := Group.IsPerfect.map (MulAut.conj g).toMonoidHom (H := B)
  have he : A.map (projection F) = (B.map (projection F)).map
      (MulAut.conj (projection F g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  refine ⟨g,?_⟩
  rcases hg with hg | hg
  · left
    let := pointLocalSL_isPerfect F hlarge
    have hh : A.map (projection F) = (pointLocalSL F).map (projection F) := he.trans hg
    exact le_antisymm (le_of_map_le_of_perfect (projection F) hker A _ hh.le)
      (le_of_map_le_of_perfect (projection F) hker _ A hh.ge)
  · right
    let := lineLocalSL_isPerfect F hlarge
    have hh : A.map (projection F) = (lineLocalSL F).map (projection F) := he.trans hg
    exact le_antisymm (le_of_map_le_of_perfect (projection F) hker A _ hh.le)
      (le_of_map_le_of_perfect (projection F) hker _ A hh.ge)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
