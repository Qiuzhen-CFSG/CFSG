module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Alternating
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.BinaryFiveSource
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The remaining small even presentations in B.4.2

The two binary linear degrees use their full natural and exterior source
recognitions. The derived binary projective symplectic group is transported
through the actual polar representation to A₆, whose complete FF source
theorem retains every permitted ambient action. These are the literal small
even constructors of Theorem C, with no additional representation premise.

Source: Aschbacher–Smith B.4.2 and K.1–3, printed pp.86 and 452–456.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem binary_linear_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) n 2) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  rcases hn with rfl | rfl
  · exact binary_four_model_case h hm
  · exact ChapterK.Linear.BinaryFiveSource.actionCase_of_source h hm

theorem binary_symplectic_derived_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ)
    (e : L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  exact alternating_case h hff (by decide : 6 ≤ 8)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
end CFSG.Quasithin.ChapterB.SourceClassification
