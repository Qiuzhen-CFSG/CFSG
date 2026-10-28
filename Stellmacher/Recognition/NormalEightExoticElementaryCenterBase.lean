module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalFourElementaryCenterBase
public import Theory.GroupTheory.C4SquareInvolutionAutomorphisms

/-!
# The elementary-center branch of the normal abelian base

For a normal four W in a Sylow two-subgroup S with no normal elementary
eight, assume C_S(W) has center W, class at most two, and exponent dividing
four. An elementary sixteen over W forces a normal self-centralizing
C₄ × C₄ base over W. The intrinsic theorem uses the square-map bound and
the uniqueness of an abelian sixteen in a group of order at most 32 with
center of order four. Its three involutions are automorphism-transitive.

The stronger local statement here needs neither ambient simplicity nor
fusion hypotheses. This completes only the elementary-center branch;
the other candidate cases remain with the characteristic-base owner.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, p.386, and the final
paragraph of p.395. No MacWilliams classification is assumed.
-/

namespace Stellmacher.Recognition.NormalEightExoticElementaryCenterBase

open Subgroup

/-- The elementary-center branch supplies an explicit C₄ × C₄ base. -/
public theorem exists_c4_square_base
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hcenter : (center (centralizer (W : Set S))).map
      (centralizer (W : Set S)).subtype = W)
    (hclass : commutator (centralizer (W : Set S)) ≤ center (centralizer (W : Set S)))
    (hexp : ∀ x : centralizer (W : Set S), x ^ 4 = 1) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
  S.isPGroup'.exists_c4_square_base_of_elementary_centralizer_center
    hno W hW B hB hWB hcenter hclass hexp

/-- The required normal abelian base, with automorphism-transitive involutions. -/
public theorem exists_normal_abelian_base
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hcenter : (center (centralizer (W : Set S))).map
      (centralizer (W : Set S)).subtype = W)
    (hclass : commutator (centralizer (W : Set S)) ≤ center (centralizer (W : Set S)))
    (hexp : ∀ x : centralizer (W : Set S), x ^ 4 = 1) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      (∀ x y : D, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut D, a x = y) := by
  obtain ⟨D, hWD, hDn, hDa, hself, ⟨e⟩⟩ :=
    exists_c4_square_base S hno W hW B hB hWB hcenter hclass hexp
  exact ⟨D, hWD, hDn, hDa, hself, e.involutions_transitive_of_c4_square⟩

end Stellmacher.Recognition.NormalEightExoticElementaryCenterBase
