module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalFourHomocyclicBase
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Stellmacher.Recognition.NormalEightExoticHomocyclicBase
public import Stellmacher.Recognition.NormalEightExoticLargeBase

/-!
# The exotic normal abelian base

Fusion of the unique normal four supplies automorphisms of its index-two
centralizer transitive on that four. Only normal elementary eights are
excluded; elementary sixteens remain available.

The homocyclic-base construction and the exclusion of larger cyclic factors
supply a homocyclic self-centralizing base with cyclic factors of order at
most four. The elementary sixteen excludes smaller factors, yielding the
desired normal `C₄ × C₄` base. The structural steps are proved in the imported
modules rather than assumed as a classification theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386, and §6,
final paragraph of p.395, which invokes MacWilliams's structural theorem.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticAbelianBase

/-- Fusion of the chosen four acts transitively on it by automorphisms of
its centralizer, even when elementary subgroups of order sixteen exist. -/
public theorem centralizer_four_automorphism_transitive
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) :
    ∀ x y : centralizer (W : Set S), (x : S) ∈ W → (y : S) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set S)), a x = y := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  have hzS : orderOf ((z : center S) : S) = 2 :=
    (orderOf_coe (z : center S)).trans ((orderOf_coe z).trans hz)
  apply S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique (z : center S) hzS (z : center S).property
  intro x y hx hy
  exact hfused x y x.property y.property
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) (x : S) x.property)
      (fun h => hx (Subtype.ext h)))
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) (y : S) y.property)
      (fun h => hy (Subtype.ext h)))

/-- Once a homocyclic base has exponent at most four, the elementary sixteen
forces it to be the required `C₄ × C₄` base. -/
public theorem c4_square_base_of_homocyclic_exponent_le_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (W : Subgroup S) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup S) (hWD : W ≤ D) (hDn : D.Normal) (hDa : IsMulCommutative D)
    (hDC : centralizer (D : Set S) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : n ≤ 2)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧ (omega₁ D (p := 2)).map D.subtype = W ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  have hn' := two_le_homocyclic_exponent_of_elementary_sixteen W hW B hB hWB D hWD hDC n e
  have heq : n = 2 := by omega
  subst n
  exact ⟨D, hWD, hDn, hDa, hDC, hO, ⟨e⟩⟩

/-- The fused normal-four setup with an elementary sixteen supplies a
self-centralizing normal `C₄ × C₄` base whose first omega is the given four. -/
public theorem exists_c4_square_base
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 →
      orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧ (omega₁ D (p := 2)).map D.subtype = W ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hO, n, _hn, ⟨e⟩⟩ :=
    NormalEightExoticHomocyclicBase.exists_homocyclic_base
      hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hn := NormalEightExoticLargeBase.homocyclic_exponent_le_two
    hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm D hWD hDC hO n e
  exact c4_square_base_of_homocyclic_exponent_le_two
    S W hW B hB hWB D hWD hDn hDa hDC hO n hn e

end Stellmacher.Recognition.NormalEightExoticAbelianBase
