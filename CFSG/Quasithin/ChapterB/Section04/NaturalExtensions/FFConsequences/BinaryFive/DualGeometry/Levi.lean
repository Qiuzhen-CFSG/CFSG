module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.DualGeometry.RankFour
public import Theory.SpecificGroups.BinaryLinear.ComplementaryLineLevi.Five

/-!
# The genuine end-node Levi placement in B.4.9

The invariant four-space and complementary fixed line supplied by the
rank-four geometry define an actual Levi complement. Its restriction to
the four-space is bijective, its ambient parabolic is maximal, and its
complement is the two-core computed inside that parabolic. Applying these
intrinsic results discharges every clause of the rank-four end-node
placement, without a splitting or additional geometry premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(iv), printed pp.94–95. Final splitting and alternatives assembly
belong to the dual-geometry consumer.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear BinaryLinear.OuterCyclic

/-- The three intrinsic clauses for the literal end-node Levi and action. -/
theorem endNodeLevi_properties (W K : Submodule (ZMod 2) (Space 5))
    (hW : Module.finrank (ZMod 2) W = 4) (hK : Module.finrank (ZMod 2) K = 1)
    (hWK : IsCompl W K) :
    IsCoatom (parabolic W) ∧
      (pCore 2 (parabolic W)).IsComplement'
        ((endNodeLevi W K).subgroupOf (parabolic W)) ∧
      Function.Bijective (endNodeAction W K) :=
  ⟨ComplementaryLineLevi.fourSpace_parabolic_isCoatom W hW,
    ComplementaryLineLevi.twoCore_isComplement W K hK hWK,
    ComplementaryLineLevi.restriction_bijective W K hK hWK⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- A dual rank-four best offender lies in a genuine end-node Levi complement,
with the faithful full restriction action retained under the original marking. -/
theorem dual_rank_four_endNodePlacement (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hr : rank A = 4) :
    EndNodePlacement d hF A := by
  obtain ⟨W, K, hW, hK, hWK, hA⟩ := dual_rank_four_block_placement d hF e hA hr
  obtain ⟨hP, hcomp, hact⟩ := endNodeLevi_properties W K hW hK hWK
  exact ⟨W, K, hW, hK, hWK, hP, hcomp, hact, hA⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
