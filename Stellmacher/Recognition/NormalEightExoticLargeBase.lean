module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightCentralizerCharacteristic
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseCharacteristic

/-!
# Excluding large homocyclic bases in the exotic normal-four case

Fusion of the unique normal four rules out characteristic subgroups of
order two in its centralizer. A self-centralizing normal homocyclic base
of exponent at least eight supplies just such a characteristic subgroup,
by the intrinsic structure theorem in `HomocyclicLargeBaseCharacteristic`.
Combining these results bounds the exponents of its cyclic factors by four.

Only normal elementary eights in the Sylow subgroup are excluded. In
particular, this argument does not assume that its index-two centralizer
has no normal elementary eight.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386, and the
final paragraph of p.395. The latter invokes MacWilliams's structure
theorem; the intrinsic structure used here is proved in the imported
group-theoretic modules.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticLargeBase

/-- Fusion excludes a characteristic involution in the centralizer of the
unique normal four, without any bound on the order of the Sylow subgroup. -/
public theorem centralizer_no_characteristic_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (K : Subgroup (centralizer (W : Set S))) [K.Characteristic] : Nat.card K ≠ 2 := by
  apply centralizer_no_characteristic_two_of_four_transitive hno W hW ?_ K
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  have hzS : orderOf ((z : center S) : S) = 2 :=
    (orderOf_coe (z : center S)).trans ((orderOf_coe z).trans hz)
  apply S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique (z : center S) hzS (z : center S).property
  intro x y hx hy
  exact hfused x y x.property y.property
    (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) (x : S) x.property)
      (fun h => hx (Subtype.ext h)))
    (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) (y : S) y.property)
      (fun h => hy (Subtype.ext h)))

/-- Fusion of the normal four excludes a self-centralizing normal homocyclic
base whose cyclic factors have order at least eight. -/
public theorem large_homocyclic_base_false
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup S) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set S) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    False := by
  obtain ⟨K, hKchar, hKcard⟩ :=
    S.isPGroup'.centralizer_exists_characteristic_two_of_large_homocyclic_base
      hZ hno W hW hunique B hB hWB D hWD hDC hO n hn e
  let : K.Characteristic := hKchar
  exact centralizer_no_characteristic_two S hZ hno W hW hunique hfused K hKcard

/-- In the exotic normal-four setup, each cyclic factor of a self-centralizing
normal homocyclic base has order at most four. -/
public theorem homocyclic_exponent_le_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (_hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D] (hWD : W ≤ D)
    (hDC : centralizer (D : Set S) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    n ≤ 2 := by
  by_contra hn
  exact large_homocyclic_base_false S hZ hno W hW hunique hfused B hB hWB
    D hWD hDC hO n (by omega) e

end Stellmacher.Recognition.NormalEightExoticLargeBase
