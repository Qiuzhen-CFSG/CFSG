module

public import Stellmacher.Recognition.NormalEightExoticAbelianBase
public import Theory.GroupTheory.PGroup.Order128C4SquareBase

/-!
# The normal C₄-square base in the Hall–Janko branch

Fusion of the unique normal four supplies automorphisms of its centralizer
transitive on that four's involutions. The intrinsic order-128 base theorem
then gives a normal self-centralizing C₄ × C₄ whose first omega is the
chosen four. The elementary sixteen is not assumed to contain that four.

This is the abelian-base step for Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(a), printed p.386, citing MacWilliams,
DOI 10.1090/S0002-9947-1970-0276324-3. Extension coordinates and generators
are separate from this construction.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticHallBase

/-- The order-128 branch has a self-centralizing normal C₄-square base
containing the chosen normal four, and with exactly that first omega. -/
public theorem exists_c4_square_base
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hcard : Nat.card S = 128) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧ (omega₁ D (p := 2)).map D.subtype = W ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
  S.isPGroup'.exists_c4_square_base_of_card_eq_128 hcard hZ hno W hW
    (NormalEightExoticAbelianBase.centralizer_four_automorphism_transitive
      S hZ hno W hW hunique hfused) B hB

end Stellmacher.Recognition.NormalEightExoticHallBase
