module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.GroupTheory.PGroup.NormalFourInvariantAbelianBase
public import Stellmacher.Recognition.NormalEightExoticCharacteristicBase

/-!
# A homocyclic base for the exotic normal-four case

Fusion of the normal four induces automorphisms of its centralizer transitive
on that four's three involutions. A characteristic abelian self-centralizing
subgroup of the centralizer therefore maps to a normal self-centralizing
homocyclic subgroup of the Sylow group, with first omega the given four.

The structural construction also supplies a normal abelian self-centralizing
base whose automorphisms are transitive on its involutions. Absence of normal
elementary eights identifies its first omega with the given four, and
transitivity forces its two cyclic factors to have equal order. This completes
existence without requiring the chosen base to be characteristic.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386, and the
final paragraph of §6, printed p.395.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticHomocyclicBase

private theorem centralizer_four_transitive
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
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (A := W) (x : S) x.property) (fun h => hx (Subtype.ext h)))
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (A := W) (y : S) y.property) (fun h => hy (Subtype.ext h)))

/-- Fusion supplies a maximal characteristic abelian homocyclic candidate
containing `W` in its ambient image. This theorem does not assert self-centrality. -/
public theorem exists_maximal_characteristic_homocyclic_candidate
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) :
    ∃ A : Subgroup (centralizer (W : Set S)), A.Characteristic ∧ IsMulCommutative A ∧
      W ≤ A.map (centralizer (W : Set S)).subtype ∧
      (∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
        IsMulCommutative A' → A ≤ A' → A' = A) ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (A.map (centralizer (W : Set S)).subtype ≃*
          (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) :=
  S.isPGroup'.exists_maximal_characteristic_abelian_homocyclic_in_four_centralizer
    hno W hW (centralizer_four_transitive S hZ hno W hW hunique hfused)

/-- Choosing a characteristic abelian self-centralizing subgroup of `C_S(W)`
completes the homocyclic-base construction. -/
public theorem homocyclic_base_of_characteristic_centralizer_base
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (hbase : ∃ A : Subgroup (centralizer (W : Set S)), A.Characteristic ∧
      IsMulCommutative A ∧ centralizer (A : Set (centralizer (W : Set S))) ≤ A) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  obtain ⟨A, hAc, hAa, hAC⟩ := hbase
  let : A.Characteristic := hAc
  let : IsMulCommutative A := hAa
  exact S.isPGroup'.exists_homocyclic_base_of_characteristic_centralizer_base
    hno W hW (centralizer_four_transitive S hZ hno W hW hunique hfused) A hAC

/-- The exotic normal-four hypotheses supply a self-centralizing homocyclic
normal abelian base with first omega exactly the given four. -/
public theorem exists_homocyclic_base
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
      centralizer (D : Set S) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, htrans⟩ :=
    NormalEightExoticCharacteristicBase.exists_normal_abelian_base
      hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWD
  have hfour : Nat.card (omega₁ D (p := 2)) = 4 := by
    have hh := congrArg (fun H : Subgroup S => Nat.card H) hO
    simpa only [card_map_of_injective D.subtype_injective, hW] using hh
  exact ⟨D, hWD, hDn, hDa, hDC, hO,
    (S.isPGroup'.to_subgroup D).exists_equiv_prod_self_zmod_of_transitive_involutions
      hfour htrans⟩

end Stellmacher.Recognition.NormalEightExoticHomocyclicBase
