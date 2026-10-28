module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections

/-!
# Orthogonal parabolic exclusions under the genuine A.2 induction hypothesis

The actual binary split orthogonal carrier in rank at least five contains
the split-eight projective group in a proper singular-root normalizer. The
marked section lifts through the literal map G → G/Z(G); smaller-section
induction and the intrinsic rank-three obstruction then give a contradiction.
No quasithinness of the central quotient is assumed.

Source: Aschbacher–Smith A.2.15(2) and A.2.18, printed pp.37–40.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
open ClassicalOrthogonal ClassicalOrthogonal.A02ParabolicSections
open Theory.SpecificGroups.LieType
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The binary plus family above rank four is excluded by its actual split-eight section. -/
theorem false_of_binary_plus_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r : ℕ} (hr : 5 ≤ r)
    (e : (G ⧸ Subgroup.center G) ≃* POmegaPlus r (ZMod 2)) : False := by
  obtain ⟨n, rfl⟩ : ∃ n, r = 4+n+1 := ⟨r-5, by omega⟩
  exact ExceptionalSections.false_of_binary_splitEight_section ih hG hK e
    (splitTailSection (F:=ZMod 2) 4 n (by omega))

/-- Source-facing rank bound; the binary rank-four endpoint has its separate local obstruction. -/
theorem binary_plus_center_quotient_rank_le_four
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r : ℕ} (e : (G ⧸ Subgroup.center G) ≃* POmegaPlus r (ZMod 2)) : r ≤ 4 := by
  by_contra hr
  exact false_of_binary_plus_center_quotient ih hG hK (by omega) e

end CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
