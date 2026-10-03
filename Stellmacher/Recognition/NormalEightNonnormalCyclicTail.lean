module

public import Stellmacher.Recognition.NormalEightNonnormalCyclicWeakClosure
public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightNonnormalCyclicCentralizer
public import Stellmacher.Recognition.NormalEightNonnormalCyclicNormalizers
public import Theory.GroupTheory.ElementaryEightCentralizerFusionObstruction

/-!
# Cyclic-tail fusion assembly with a normal-only elementary bound

Core weak closure and Z-star produce an outside conjugate of a central
Sylow involution. Saturating this choice gives an elementary centralizer
of order eight. Its ambient normalizer is solvable by N₂, while every
elementary eight has Sylow normalizer of order thirty-two. The automizer
obstruction then excludes a large cyclic tail. Neither intrinsic width
one nor Sylow noncommutativity is needed beyond the displayed factorization.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The remaining outside-conjugate exclusion completes the cyclic-tail bound.
This interface leaves the local centralizer and automizer argument explicit. -/
public theorem omegaQuotient_cyclic_tail_card_lt_eight_of_outside_exclusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤)
    (houter : 8 ≤ Nat.card D → ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) → False) :
    Nat.card D < 8 := by
  by_contra! hlarge
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t, ht, hconj⟩ := exists_conjugate_outside_core_of_large_cyclic_tail
    hns hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge z hzC hz
  exact houter hlarge z t hzC hz ht hconj

/-- A large cyclic Hall tail is excluded by the saturated elementary-eight
centralizer and its solvable automizer. The displayed factorization suffices;
no intrinsic width-one premise is needed. -/
public theorem omegaQuotient_cyclic_tail_card_lt_eight
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] [IsCyclic D] (hB : Nat.card B = 8)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hgen : B ⊔ D = ⊤)
    (_hwidth : ∀ B' D' : Subgroup (pCore 2 (OmegaQuotient S)),
      B'.Normal → D'.Normal → IsExtraspecial 2 B' → IsBinaryHallFactor D' →
      D' ≤ centralizer (B' : Set (pCore 2 (OmegaQuotient S))) →
      B' ⊔ D' = ⊤ → Nat.card B' = 8) :
    Nat.card D < 8 := by
  by_contra! hlarge
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  obtain ⟨t', _, hconj', hElem', hcard', hsat'⟩ :=
    exists_saturated_elementary_eight_centralizer_of_large_cyclic_tail
      hns hN S A hA hZ W hW hno hunique hnormal B D hB hc hgen hlarge z hzC hz
  let E : Subgroup S := centralizer ({t'} : Set S)
  let : IsElementaryAbelian 2 E := hElem'
  let U : Subgroup G := E.map (S : Subgroup G).subtype
  have hUcard : Nat.card U = 8 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hcard'
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hUcard
    omega
  have hsol : Group.IsSolvable (normalizer (U : Set G)) := by
    exact hN _ ⟨U, hUne, IsElementaryAbelian.isPGroup 2 U, rfl⟩
  exact Sylow.false_of_saturated_elementary_eight_centralizer
    S z t' hzC hz hconj' E rfl hcard' hsol
    (by simpa [U, E] using hsat')
    (fun F hF hFc => card_elementary_eight_normalizer_eq_thirty_two_of_cyclic_tail
      hN S hZ W hW hno hunique hnormal B D hB hc hgen hlarge F hF hFc)

end Stellmacher.Recognition.NormalEightNonnormalImage
