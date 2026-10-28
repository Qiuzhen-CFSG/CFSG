module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.C4SquareIndexEight
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion
public import Theory.SpecificGroups.MacWilliams.HallJankoIntrinsicRecognition
public import Stellmacher.Recognition.HallJankoTrivialSylowAutomizer

/-!
# Exclusion of the order-128 C₄-square extension

The four-centralizer is the product of the elementary sixteen and the normal
C₄-square, of order 64. Ambient fusion induces automorphisms of this
centralizer, so the square-root fibers of its three marked involutions have
equal cardinality. For the final exclusion, intrinsic extension recognition
identifies the Sylow subgroup with the Hall–Janko presentation. The checked
ambient fusion and transfer argument then contradicts the marked fused four.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4 and §6, printed pp.386,
395. The exclusion in the source invokes MacWilliams's classification.
-/

namespace Stellmacher.Recognition.NormalEightExoticExtension128

open Subgroup

/-- The order hypothesis identifies the four-centralizer and its order. -/
public theorem centralizer_structure_of_card_eq_128
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W D B : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hcard : Nat.card S = 128) :
    D.index = 8 ∧ centralizer (W : Set S) = B ⊔ D ∧
      Nat.card (centralizer (W : Set S)) = 64 := by
  have hC := C4SquareExtension.centralizer_eq_sup_of_card_eq_128
    S.isPGroup' hZ W D B hW hB hWB hO hmodel hcard
  refine ⟨C4SquareExtension.index_eq_eight_of_card_eq_128 D hmodel hcard, hC, ?_⟩
  rw [hC]
  exact C4SquareExtension.card_sup_eq_sixty_four W D B hW hB hWB hO hmodel

/-- Fusion makes the square-root fibers of the three marked involutions equal.
The automorphism is obtained by Sylow transport, without choosing its order. -/
public theorem centralizer_square_fibers_eq
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (x y : centralizer (W : Set S)) (hxW : (x : S) ∈ W) (hyW : (y : S) ∈ W)
    (hx : orderOf x = 2) (hy : orderOf y = 2) :
    Nat.card {a : centralizer (W : Set S) // a ^ 2 = x} =
      Nat.card {a : centralizer (W : Set S) // a ^ 2 = y} := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 :=
    (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzc : z ∈ center S := (w : center S).property
  have hfusion (u v : W) (hu : u ≠ 1) (hv : v ≠ 1) :
      IsConj ((u : S) : G) ((v : S) : G) := by
    apply hfused u v u.property v.property
    · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (u : S) u.property)
        (fun h => hu (Subtype.ext h))
    · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (v : S) v.property)
        (fun h => hv (Subtype.ext h))
  obtain ⟨f, hf⟩ := S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique z hz hzc hfusion x y hxW hyW hx hy
  apply Nat.card_congr
  exact {
    toFun := fun a => ⟨f a, by rw [← map_pow, a.property, hf]⟩
    invFun := fun a => ⟨f.symm a, by rw [← map_pow, a.property, ← hf, f.symm_apply_apply]⟩
    left_inv := fun a => Subtype.ext (f.symm_apply_apply a)
    right_inv := fun a => Subtype.ext (f.apply_symm_apply a) }

/-- The C₄-square extension cannot have order 128 in the marked ambient
configuration. Intrinsic recognition discharges the explicit-model hypothesis
of the Hall–Janko fusion exclusion. -/
public theorem false_of_card_eq_128
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (hcard : Nat.card S = 128) : False := by
  have hSmodel := MacWilliamsSylow.nonempty_hallJanko_equiv_of_c4Square
    S.isPGroup' hcard hZ hno W D hW hWD hDC hDO hmodel B hB
  exact HallJankoTrivialSylowAutomizer.false_of_trivial_sylow_automizer
    hns hN S hSmodel hnorm hZ hno W hW hunique hfused B hB hWB

end Stellmacher.Recognition.NormalEightExoticExtension128
