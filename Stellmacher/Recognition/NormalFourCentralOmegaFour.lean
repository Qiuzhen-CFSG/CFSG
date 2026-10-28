module

public import Stellmacher.Recognition.NormalFourSylowReduction
public import Stellmacher.Recognition.NormalFourCentralFusion
public import Stellmacher.Recognition.NormalFourMacWilliams
public import Theory.Frattini.BinarySquares

/-!
# The central-four structural assembly

The fusion results in `NormalFourCentralFusion` rule out the trivial
normalizer action and prove transitivity on the three involutions. The
intrinsic calculation in `NormalFourMacWilliams` then gives order 64 and
identifies the center, commutator and Frattini subgroups. The square-generated
subgroup equals the Frattini subgroup in any finite two-group, so these
equalities give the full `IsLyonsSylow` predicate. The rank bound also supplies
the first omega equality needed by Lyons's full `SylowStructure` interface.

This completes the central-four case of Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3 and Lemma 5.1, pp.386 and 393–394, without invoking an ambient
classification. The N₂ hypothesis is unnecessary for this specialization.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaFour

open Subgroup

/-- The square equality in the Lyons interface follows from the Frattini
equality. The remaining assumptions are the structural conclusion of the
MacWilliams step. -/
public theorem isLyonsSylow_of_structural_equalities
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 64)
    (hderived : center P = commutator P) (hfrattini : center P = frattini P)
    (helem : IsElementaryAbelian 2 (center P)) (hcenter : Nat.card (center P) = 4) :
    IsLyonsSylow P :=
  (isLyonsSylow_iff P).mpr ⟨center P, hcard, rfl, hderived, hfrattini,
    hfrattini.trans hP.frattini_eq_closure_squares, helem, hcenter⟩

/-- A nonabelian Sylow two-subgroup with central first omega of order four
satisfies the Lyons predicate under the ambient elementary rank bound.
The N₂ hypothesis is not needed. -/
public theorem isLyonsSylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    IsLyonsSylow S := by
  obtain ⟨hc, hd, hf, he, hZ⟩ :=
    NormalFourMacWilliams.structural_equalities hns S hrank hnonab hfour
  exact isLyonsSylow_of_structural_equalities S.isPGroup' hc hd hf he hZ

/-- The central-four case also supplies Lyons's full intrinsic structure,
including equality of the center with the first omega subgroup. -/
public theorem sylowStructure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hnonab : ¬ IsMulCommutative S)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4) :
    LyonsU3Four.SylowStructure S :=
  (isLyonsSylow hns S hrank hnonab hfour).sylowStructure_of_elementary_card_lt_eight S hrank

end Stellmacher.Recognition.NormalFourCentralOmegaFour
