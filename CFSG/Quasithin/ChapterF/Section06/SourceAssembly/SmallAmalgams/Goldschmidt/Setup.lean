module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Theory.GroupAction.RankTwoCosetGeometry
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The faithful cubic amalgams used by Goldschmidt's classification

The finite source amalgam retains its literal overlap and both inclusion maps.
The tree-action interface records the hypotheses of the geometric argument,
without including an enumeration, size bound, or finite-interval conclusion.
Its two-perfect specialization concerns the acting group on the universal tree;
it must not be inferred from two-perfectness of an arbitrary finite completion.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), pp.377--379,
386--387, and the standing hypotheses of Sections 4--6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

/-- The literal subgroup amalgam, in the order chosen by the source. -/
abbrev inclusionAmalgam {G : Type*} [Group G] (A B : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right

/-- The finite binary cubic input; all fields are original local hypotheses. -/
structure PrimitiveCubic {L D R : Type*} [Group L] [Group D] [Group R]
    (α : RankTwoAmalgam L D R) : Prop where
  sylow : RankTwoAmalgam.SylowEmbedded 2 α
  faithful : RankTwoAmalgam.Faithful α
  left_index : α.left.range.index = 3
  right_index : α.right.range.index = 3

/-- The original F.6 triple supplies the entire finite cubic source input. -/
theorem primitiveCubic_of_goldschmidt {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    PrimitiveCubic (inclusionAmalgam A B) := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hs : RankTwoAmalgam.SylowEmbedded 2 (inclusionAmalgam A B) :=
    RankTwoAmalgam.sylowEmbedded_ofSubgroups S A (A ⊓ B) B inf_le_left inf_le_right hS
  refine ⟨hs, h.amalgam_faithful hcore, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hs.left_sylow
    rw [← hP]
    exact SymmetricThreeTwoCore.sylow_index_three h.quotient_left.some P
  · obtain ⟨P, hP⟩ := hs.right_sylow
    rw [← hP]
    exact SymmetricThreeTwoCore.sylow_index_three h.quotient_right.some P

/-- Goldschmidt's geometric hypotheses on the actual rank-two coset action.
Finiteness is local; the universal completion itself is infinite. -/
structure CubicTreeAction {G : Type*} [Group G] (F : Bool → Subgroup G) : Prop where
  finite : ∀ i, Finite (F i)
  generated : F false ⊔ F true = ⊤
  primitive : PrimitiveCubic (inclusionAmalgam (F false) (F true))
  tree : (Subgroup.CosetGeometry.RankTwo.graph F).IsTree

/-- This is the two-perfect universal-tree action of Goldschmidt Sections 4--6. -/
structure TwoPerfectTreeAction {G : Type*} [Group G] (F : Bool → Subgroup G)
    : Prop extends CubicTreeAction F where
  twoPerfect : IsPPerfect 2 G

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
