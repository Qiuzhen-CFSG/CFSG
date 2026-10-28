module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.ExteriorFive
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SL2G2Source
/-!
# The split irreducible catalogue in B.5.13

The actual central quotient identifies with the moved module when that module
complements the component-fixed space. Every corrected B.4.2 row then gives
the dual ratio bound: central-cover geometry handles SL₂, Sp₄ and G₂, the
SL₃ graph automorphism handles its field family, and dimension or end-node
rank bounds handle the remaining rows.

Source: Aschbacher–Smith B.5.13, printed pp.110–111, using B.4.2.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences SourceInduction.ProjectiveLine
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem irreducible_moved_bound [Group.IsPerfect L] [Nontrivial L]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) (hff : IsFFModule ρ)
    (hcase : SourceInduction.ProjectiveLine.IrreducibleActionCase s.action L (offenderSubgroup s.action)) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  cases hcase with
  | linearTwo F hg e ho hr =>
    exact linearTwo_moved_dual_ratio_le_two s hi F (linearTwo_field_large F e) ⟨e⟩
  | linearThree F hg e hr => exact linearThree_moved_dual_bound s hc hff hg F e
  | symplectic F hl hg e hr => exact symplectic_moved_dual_ratio_le_two s hi F hl e
  | symplecticTwo e hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.action.linearEquiv.finrank_eq]
    norm_num [Module.finrank_pi]
  | g2 F hl hg e ho hr => exact g2_moved_dual_ratio_le_two s hi F ⟨e⟩
  | g2Two e ho hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.action.linearEquiv.finrank_eq, Atlas.G2.Natural.finrank_space]
    decide
  | symmetric n hn e ho hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.action.linearEquiv.finrank_eq]
    rcases hn with rfl | rfl
    · rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]; decide
    · rw [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)]; decide
  | alternatingSix hg e ho hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.linearEquiv.finrank_eq, BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  | alternatingSeven hg hL e hd ho hr =>
    apply small_moved_dual_bound s hc hff
    omega
  | tripleSix hg act hr =>
    apply small_moved_dual_bound s hc hff
    rw [act.dimension]
    decide
  | binaryLinear d hd hg e hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (Fin d → ZMod 2) ≤ 9
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega
  | orthogonalSix hg hL e ho hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.linearEquiv.finrank_eq, BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
    decide
  | symmetricEight hH e hr =>
    apply small_moved_dual_bound s hc hff
    rw [e.action.linearEquiv.finrank_eq, BinaryPermutation.finrank_natural_even (Fin 8) (by decide)]
    decide
  | exteriorFive hg hL e hd ho hr => exact exteriorFive_moved_dual_bound s hc hff hg hL e hd ho
end CFSG.Quasithin.ChapterB.SourceB513
