module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound

/-!
# The source orbit bound for actual C-components

Distinct C-components commute in the two-core quotient. The odd-rank bound
allows at most two conjugates, and solvable-quotient transport preserves the
normalizer index. This proves the orbit part of 1.2.1(3) directly, without
assuming its separate model list.
Source: Aschbacher–Smith A.3.7–8 and 1.2.1(3), printed pp.45–46 and504.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Every actual C-component is normal or has precisely two conjugates. -/
theorem proposition_1_2_1_three_orbit_source
    (hQ : IsSQTK κ (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  let := pCore_isNilpotent (p := 2) (G := G)
  have hbar := ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput κ)
    hQ (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient (pCore 2 G))
  rcases hbar with hn | hi
  · exact Or.inl (cComponent_normal_of_quotient_normal hB (pCore 2 G) hn)
  · exact Or.inr ((cComponent_normalizer_index_quotient hB (pCore 2 G)).symm.trans hi)

end CFSG.Quasithin.Chapter1.Section02
