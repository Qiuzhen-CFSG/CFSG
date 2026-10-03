module

public import Theory.GroupTheory.PGroup.Order128AbelianBase
public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Stellmacher.Recognition.NormalEightExoticHallBase
public import Theory.SpecificGroups.MacWilliams.HallJankoExtension

/-!
# Hall–Janko generators in the order-128 branch

In the order-128 branch, extend the normal four to a self-centralizing normal
abelian subgroup. Its omega subgroup is the given four. The elementary sixteen
and the unique central involution force its index to exceed four, so its two
nontrivial cyclic factors have exponents whose sum is at most four.

Fusion of the unique normal four selects a C₄-square base. The intrinsic
extension theorem constructs and normalizes its action frame, giving the exact
seven generators of `hallJankoTable`. The order 128 is an explicit input.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
and MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticHallGenerators

open Subgroup

/-- The order-128 hypothesis bounds the actual normal abelian base by sixteen.
The elementary sixteen need not contain the chosen normal four. -/
public theorem exists_small_base
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hcard : Nat.card S = 128)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧ Nat.card D ≤ 16 ∧ 4 < D.index ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ n + m ≤ 4 ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :=
  S.isPGroup'.exists_small_normal_abelian_base_of_card_eq_128 hcard hZ hno W hW B hB

/-- Fusion of the unique normal four and the order-128 hypothesis give
generators satisfying every square and right-commutator in the Hall–Janko
table. Ambient simplicity and the normalizer inequality are not needed once
these local hypotheses are supplied. -/
public theorem exists_generators
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
    ∃ x : Fin 7 → S, MacWilliamsSylow.Relations MacWilliamsSylow.hallJankoTable x ∧
      Subgroup.closure (Set.range x) = ⊤ := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hDO, hmodel⟩ :=
    NormalEightExoticHallBase.exists_c4_square_base S hZ hno W hW hunique hfused B hB hcard
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  exact MacWilliamsSylow.exists_hallJanko_generators_of_c4_square_base
    S.isPGroup' hcard hZ hno W D hW hWD hDC hDO hmodel B hB

end Stellmacher.Recognition.NormalEightExoticHallGenerators
