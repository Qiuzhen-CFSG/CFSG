module

public import Stellmacher.SectionOne.NineCoreSupportDecompositionCountingLines
public import Stellmacher.SectionOne.NineCoreSupportDecompositionCountingGeometry

/-!
# Intrinsic order-four support decomposition

For a faithful elementary-nine action on an elementary sixteen, exactly two
order-three lines have order-four fixed subgroups. The geometry of distinct
supporting lines then gives complementary supports and characterizes all
intrinsic supports.

Source: Stellmacher, *On the 2-local structure of N-groups*, printed p.47,
(9.1)(8).
-/

@[expose] public section

universe u

namespace Stellmacher.SectionOne

theorem nineCoreSupportDecomposition_intrinsic_pair
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (W : Subgroup K) (hWelementary : IsElementaryAbelian 3 W)
    (hWcard : Nat.card W = 9) (hVcard : Nat.card V = 16)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥) :
    ∃ first second : Subgroup V, IsCompl first second ∧
      ∀ support : Subgroup V,
        NineCoreSupportDecompositionIntrinsic W support ↔
          support = first ∨ support = second := by
  exact nineCoreSupportDecomposition_intrinsic_pair_of_supporting_lines_card
    W hWcard hVcard hfaith
    (nineCoreSupportDecomposition_supporting_lines_card W hWelementary hWcard hVcard hfaith)

end Stellmacher.SectionOne
