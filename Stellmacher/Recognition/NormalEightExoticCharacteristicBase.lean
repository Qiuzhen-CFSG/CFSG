module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.GroupTheory.PGroup.NormalFourInvariantAbelianBase
public import Theory.GroupTheory.PGroup.MaximalCharacteristicAbelianCenter
public import Stellmacher.Recognition.NormalEightExoticElementaryCenterBase
public import Stellmacher.Recognition.NormalEightExoticThickCandidateBase

/-!
# Characteristic abelian candidates in the four-centralizer

Ambient fusion of the unique normal four gives transitive automorphisms of
its centralizer. Thus a maximal characteristic abelian subgroup containing
the four can be chosen homocyclic. If this candidate has order four, it is
the center, and the centralizer has class at most two and exponent at most
four. These reductions do not assert that the candidate is self-centralizing.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386, and the
final paragraph of §6, printed p.395. The structural existence step cited
there is due to MacWilliams and is not assumed here.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticCharacteristicBase

variable {G : Type*} [Group G] [Finite G]

/-- Fusion on the given four supplies the exact transitivity needed by the
invariant abelian candidate construction. -/
public theorem centralizer_four_transitive
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
  have hzS : orderOf ((z : center S) : S) = 2 := by
    simpa only [orderOf_coe] using hz
  apply S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique z hzS (z : center S).property
  intro x y hx hy
  apply hfused x y x.property y.property
  · exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ x.property)
      (fun h => hx (Subtype.ext h))
  · exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ y.property)
      (fun h => hy (Subtype.ext h))

/-- The fused four has a maximal characteristic abelian homocyclic
overgroup in its centralizer. -/
public theorem exists_maximal_candidate
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
          (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :=
  S.isPGroup'.exists_maximal_characteristic_abelian_homocyclic_in_four_centralizer
    hno W hW (centralizer_four_transitive S hZ hno W hW hunique hfused)

/-- An order-four maximal candidate is the center, and the centralizer has
class at most two and exponent at most four. -/
public theorem class_two_of_candidate_card_four
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (A : Subgroup (centralizer (W : Set S)))
    (hWA : W ≤ A.map (centralizer (W : Set S)).subtype)
    (hmax : ∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
      IsMulCommutative A' → A ≤ A' → A' = A)
    (hA : Nat.card A = 4) :
    (center (centralizer (W : Set S))).map (centralizer (W : Set S)).subtype = W ∧
      commutator (centralizer (W : Set S)) ≤ center (centralizer (W : Set S)) ∧
      ∀ x : centralizer (W : Set S), x ^ 4 = 1 := by
  let C := centralizer (W : Set S)
  have hAW : A.map C.subtype = W :=
    (eq_of_le_of_card_ge hWA (by rw [card_map_of_injective C.subtype_injective, hA, hW])).symm
  have hAZ : A ≤ center C := by
    intro a ha
    have haW : (a : S) ∈ W := hAW.le (mem_map_of_mem C.subtype ha)
    exact mem_center_iff.mpr (fun c => Subtype.ext (c.property a haW).symm)
  have hZA : center C = A := hmax _ inferInstance inferInstance hAZ
  have hcenter : (center C).map C.subtype = W := by rw [hZA, hAW]
  have hmaxZ : ∀ A' : Subgroup C, A'.Characteristic → IsMulCommutative A' →
      center C ≤ A' → A' = center C := by
    simpa only [hZA] using hmax
  let : IsElementaryAbelian 2 (center C) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z => by
        apply Subtype.ext
        apply Subtype.ext
        exact elemPow_eq_one_of_isElementaryAbelian _
          (hcenter.le (mem_map_of_mem C.subtype z.property))) }
  exact ⟨hcenter,
    (S.isPGroup'.to_subgroup C).commutator_le_center_of_maximal_characteristic_abelian_center hmaxZ,
    (S.isPGroup'.to_subgroup C).exponent_four_of_maximal_characteristic_abelian_center hmaxZ⟩

/-- Reduction of base existence to the elementary-center case and the case
of a maximal characteristic candidate with cyclic factors of order at least
four. Neither structural case is assumed to follow merely from maximality. -/
public theorem exists_base_of_candidate_cases
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (hsmall :
      (center (centralizer (W : Set S))).map (centralizer (W : Set S)).subtype = W →
      commutator (centralizer (W : Set S)) ≤ center (centralizer (W : Set S)) →
      (∀ x : centralizer (W : Set S), x ^ 4 = 1) →
      ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
        centralizer (D : Set S) ≤ D ∧
        ∀ x y : D, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut D, a x = y)
    (hlarge : ∀ A : Subgroup (centralizer (W : Set S)),
      A.Characteristic → IsMulCommutative A →
      W ≤ A.map (centralizer (W : Set S)).subtype →
      (∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
        IsMulCommutative A' → A ≤ A' → A' = A) →
      ∀ n : ℕ, 2 ≤ n →
      (A.map (centralizer (W : Set S)).subtype ≃*
        (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) →
      ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
        centralizer (D : Set S) ≤ D ∧
        ∀ x y : D, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut D, a x = y) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      ∀ x y : D, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut D, a x = y := by
  obtain ⟨A, hAc, hAa, hWA, hmax, n, hn, ⟨e⟩⟩ :=
    exists_maximal_candidate S hZ hno W hW hunique hfused
  by_cases hn2 : 2 ≤ n
  · exact hlarge A hAc hAa hWA hmax n hn2 e
  · have hn1 : n = 1 := by omega
    have hA : Nat.card A = 4 := by
      have hh := Nat.card_congr e.toEquiv
      rw [card_map_of_injective (centralizer (W : Set S)).subtype_injective] at hh
      simpa [hn1, Nat.card_prod] using hh
    obtain ⟨hcenter, hclass, hexp⟩ := class_two_of_candidate_card_four S W hW A hWA hmax hA
    exact hsmall hcenter hclass hexp

/-! The intrinsic branch reductions now supply the premises of
`exists_base_of_candidate_cases`.  The result is stated in the normal-base
form accepted by the downstream homocyclic transport: characteristicity of a
candidate is only needed to prove the thick branch, while the resulting base
itself is normal in the Sylow subgroup. -/

public theorem exists_normal_abelian_base
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
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
    (_hnorm : Subgroup.normalizer (S : Set G) = (S : Subgroup G) ⊔
      Subgroup.centralizer (S : Set G)) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      Subgroup.centralizer (D : Set S) ≤ D ∧
      (∀ x y : D, orderOf x = 2 → orderOf y = 2 →
        ∃ a : MulAut D, a x = y) := by
  let hsmall :
      (center (centralizer (W : Set S))).map (centralizer (W : Set S)).subtype = W →
      commutator (centralizer (W : Set S)) ≤ center (centralizer (W : Set S)) →
      (∀ x : centralizer (W : Set S), x ^ 4 = 1) →
      ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
        centralizer (D : Set S) ≤ D ∧
        (∀ x y : D, orderOf x = 2 → orderOf y = 2 →
          ∃ a : MulAut D, a x = y) := by
    intro hcenter hclass hexp
    exact NormalEightExoticElementaryCenterBase.exists_normal_abelian_base
      S hno W hW B hB hWB hcenter hclass hexp
  let hlarge : ∀ A : Subgroup (centralizer (W : Set S)), A.Characteristic →
      IsMulCommutative A → W ≤ A.map (centralizer (W : Set S)).subtype →
      (∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
        IsMulCommutative A' → A ≤ A' → A' = A) →
      ∀ n : ℕ, 2 ≤ n →
      (A.map (centralizer (W : Set S)).subtype ≃*
        (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) →
      ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
        centralizer (D : Set S) ≤ D ∧
        (∀ x y : D, orderOf x = 2 → orderOf y = 2 →
          ∃ a : MulAut D, a x = y) := by
    intro A hAc hAa hWA hmax n hn e
    exact NormalEightExoticThickCandidateBase.exists_base_of_critical_involutions
      S hZ hno W hW hunique hfused A hWA hmax n hn e
  exact exists_base_of_candidate_cases S hZ hno W hW hunique hfused hsmall hlarge

end Stellmacher.Recognition.NormalEightExoticCharacteristicBase
