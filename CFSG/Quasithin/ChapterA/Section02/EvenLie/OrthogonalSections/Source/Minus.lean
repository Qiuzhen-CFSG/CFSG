module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.Minus
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections

/-!
# The binary minus parabolic exclusion from source A.2 induction

Complement extension embeds the actual minus-six commutator group into every
larger minus carrier and retains its projective quotient. Its image lies in
the proper normalizer of an explicit nontrivial two-group. The literal section
lifts to the original group, where the proper-section induction hypothesis
contradicts the intrinsic three-rank of the binary minus-six simple group.

Source: Aschbacher–Smith A.2.15(2) and A.2.18, printed pp.37–40.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
open ClassicalOrthogonal.A02ParabolicSections
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual binary minus-six parabolic section excludes every rank at least four. -/
theorem false_of_binary_minus_center_quotient
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r : ℕ} (hr : 4 ≤ r)
    (e : (G ⧸ Subgroup.center G) ≃* ClassicalGroup.POmegaMinus r (ZMod 2)) : False := by
  obtain ⟨n,rfl⟩ : ∃ n, r = 3+n+1 := ⟨r-4,by omega⟩
  exact ExceptionalSections.false_of_binary_minusSix_section ih hG hK e
    (MinusTail.minusTailSection (F:=ZMod 2) n)

theorem binary_minus_center_quotient_rank_le_three
    {K : GroupClass.{u}} (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r : ℕ} (e : (G ⧸ Subgroup.center G) ≃* ClassicalGroup.POmegaMinus r (ZMod 2)) : r ≤ 3 := by
  by_contra hr
  exact false_of_binary_minus_center_quotient ih hG hK (by omega) e

end CFSG.Quasithin.ChapterA.Section02.EvenLie.OrthogonalSections
