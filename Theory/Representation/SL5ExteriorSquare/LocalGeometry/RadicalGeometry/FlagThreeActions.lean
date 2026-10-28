module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FlagThreeActions.Images

/-!
# The two flag three-spaces in the binary exterior square

The actual flag group preserves V₃ = Λ²Γ₃ and V₃' = Γ₁ ∧ Γ₄. In the marked
wedge bases both restricted actions are upper unitriangular. Elementary images
have binary rank at most two; an image of rank two has V₁ in its commutator.
Applying the small-index fixed-space equality to the pointwise kernel gives
the A₃ centralization and A₂ rank-two conclusions used in the source.

Source: Aschbacher--Smith, 12.5.7 and 12.5.10, printed pp.820--821
(PDF pp.837--838), with the fixed-space equality clause of E.3.8.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional BinaryOffender

/-- Upper-unitriangular action on the ordered basis (12,13,23) of V₃. -/
theorem flag_action_V₃ {g : Group} (hg : g ∈ flagGroup) (x y z : ZMod 2) :
    exteriorAction 2 g (x • basis 0 + y • basis 1 + z • basis 4) =
      (x + g.val 1 2 * y + (g.val 0 1 * g.val 1 2 + g.val 0 2) * z) • basis 0 +
        (y + g.val 0 1 * z) • basis 1 + z • basis 4 := by
  simpa [FlagThreeActions.embedding, FlagThreeActions.third, FlagThreeActions.parameters,
    FlagThreeActions.upper] using FlagThreeActions.action_embedding true hg ![x,y,z]

/-- Upper-unitriangular action on the ordered basis (12,13,14) of V₃'. -/
theorem flag_action_V₃' {g : Group} (hg : g ∈ flagGroup) (x y z : ZMod 2) :
    exteriorAction 2 g (x • basis 0 + y • basis 1 + z • basis 2) =
      (x + g.val 1 2 * y + g.val 1 3 * z) • basis 0 +
        (y + g.val 2 3 * z) • basis 1 + z • basis 2 := by
  simpa [FlagThreeActions.embedding, FlagThreeActions.third, FlagThreeActions.parameters,
    FlagThreeActions.upper] using FlagThreeActions.action_embedding false hg ![x,y,z]

/-- The genuine setwise stabilizer contains the flag group. -/
theorem flagGroup_stabilizes_V₃ :
    flagGroup ≤ BinaryOffender.subspaceStabilizer (exteriorAction 2) V₃ :=
  FlagThreeActions.stable true

/-- The genuine setwise stabilizer contains the flag group. -/
theorem flagGroup_stabilizes_V₃' :
    flagGroup ≤ BinaryOffender.subspaceStabilizer (exteriorAction 2) V₃' :=
  FlagThreeActions.stable false

variable {A : Subgroup Group}

/-- Binary rank bound for the actual image on V₃. -/
theorem rank_restricted_V₃_le_two [IsElementaryAbelian 2 A] (hA : A ≤ flagGroup) :
    rank (restrictedSubgroup (exteriorAction 2) V₃ A) ≤ 2 :=
  FlagThreeActions.image_rank_le_two true A hA

/-- Binary rank bound for the actual image on V₃'. -/
theorem rank_restricted_V₃'_le_two [IsElementaryAbelian 2 A] (hA : A ≤ flagGroup) :
    rank (restrictedSubgroup (exteriorAction 2) V₃' A) ≤ 2 :=
  FlagThreeActions.image_rank_le_two false A hA

/-- The source commutator line, with the literal exterior action and subgroup. -/
theorem V₁_le_commutator_V₃_of_image_rank_two (hA : A ≤ flagGroup)
    (hr : rank (restrictedSubgroup (exteriorAction 2) V₃ A) = 2) :
    V₁ ≤ subspaceCommutator (exteriorAction 2) V₃ A :=
  FlagThreeActions.line_le_commutator true A hA hr

/-- The same commutator line for the second flag three-space. -/
theorem V₁_le_commutator_V₃'_of_image_rank_two (hA : A ≤ flagGroup)
    (hr : rank (restrictedSubgroup (exteriorAction 2) V₃' A) = 2) :
    V₁ ≤ subspaceCommutator (exteriorAction 2) V₃' A :=
  FlagThreeActions.line_le_commutator false A hA hr

/-- The two centralizations used in 12.5.7, from the exact E.3.8 equality property. -/
theorem fixes_threeSpaces_of_smallIndex_three [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 3 A) :
    V₃ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A ∧ V₃' ≤ BinaryOffender.fixedSpace (exteriorAction 2) A :=
  ⟨FlagThreeActions.fixed_of_property_three true A hA hk,
    FlagThreeActions.fixed_of_property_three false A hA hk⟩

/-- The noncentral V₃ alternative in 12.5.10 has actual image rank two. -/
theorem rank_restricted_V₃_eq_two_of_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : ¬ V₃ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) :
    rank (restrictedSubgroup (exteriorAction 2) V₃ A) = 2 :=
  FlagThreeActions.rank_two_of_property_two true A hA hk hn

/-- The noncentral V₃' alternative in 12.5.10 has actual image rank two. -/
theorem rank_restricted_V₃'_eq_two_of_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : ¬ V₃' ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) :
    rank (restrictedSubgroup (exteriorAction 2) V₃' A) = 2 :=
  FlagThreeActions.rank_two_of_property_two false A hA hk hn

/-- Equivalent formulation using nontriviality of the genuine restricted image. -/
theorem rank_restricted_V₃_eq_two_of_image_ne_bot [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : restrictedSubgroup (exteriorAction 2) V₃ A ≠ ⊥) :
    rank (restrictedSubgroup (exteriorAction 2) V₃ A) = 2 :=
  rank_restricted_V₃_eq_two_of_smallIndex_two hA hk
    ((FlagThreeActions.image_ne_bot_iff true A hA).mp hn)

/-- Equivalent formulation for the genuine image on V₃'. -/
theorem rank_restricted_V₃'_eq_two_of_image_ne_bot [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : restrictedSubgroup (exteriorAction 2) V₃' A ≠ ⊥) :
    rank (restrictedSubgroup (exteriorAction 2) V₃' A) = 2 :=
  rank_restricted_V₃'_eq_two_of_smallIndex_two hA hk
    ((FlagThreeActions.image_ne_bot_iff false A hA).mp hn)

/-- The commutator conclusion of the noncentral V₃ branch of 12.5.10. -/
theorem V₁_le_commutator_V₃_of_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : ¬ V₃ ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) :
    V₁ ≤ subspaceCommutator (exteriorAction 2) V₃ A :=
  V₁_le_commutator_V₃_of_image_rank_two hA
    (rank_restricted_V₃_eq_two_of_smallIndex_two hA hk hn)

/-- The commutator conclusion for the second three-space in 12.5.10. -/
theorem V₁_le_commutator_V₃'_of_smallIndex_two [IsElementaryAbelian 2 A]
    (hA : A ≤ flagGroup) (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : ¬ V₃' ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) :
    V₁ ≤ subspaceCommutator (exteriorAction 2) V₃' A :=
  V₁_le_commutator_V₃'_of_image_rank_two hA
    (rank_restricted_V₃'_eq_two_of_smallIndex_two hA hk hn)
end Representation.SL5ExteriorSquare
