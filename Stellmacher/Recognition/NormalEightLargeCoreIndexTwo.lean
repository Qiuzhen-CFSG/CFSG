module

public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoSetup
public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoInside
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoGeometry
public import Theory.GroupTheory.ElementaryEightCentralizerFusionObstruction

/-!
# Normal-only index-two large-core fusion assembly

Inside-core weak closure produces an outside conjugate with an elementary
centralizer of order eight. The local geometry identifies its core intersection
with the unique normal four. The normalizer obstruction must exclude that
configuration; existence of the elementary eight alone is not a contradiction.

Inside-core nonfusion and saturation discharge the ambient obligations. Every
elementary eight has Sylow normalizer of order thirty-two, and the N₂ condition
makes its ambient normalizer solvable. The automizer obstruction now gives the
contradiction for both extraspecial types, using only the normal-elementary bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389,
the paragraph beginning “Suppose |T:H|=2”.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Final assembly separates inside-core fusion from the ambient obstruction
to the resulting elementary-eight centralizer. Both hypotheses remain obligations. -/
public theorem large_core_index_two_false_of_inside_fusion_and_outer_exclusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (houter : ∀ z t : S, orderOf z = 2 → z ∈ center S → z ∈ omegaCorePreimage S →
      orderOf t = 2 → t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) →
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) →
      omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W →
      centralizer ({t} : Set S) = W ⊔ zpowers t →
      Nat.card (centralizer ({t} : Set S)) = 8 →
      centralizer (centralizer ({t} : Set S) : Set S) = centralizer ({t} : Set S) → False) :
    False := by
  obtain ⟨z, t, hz, hzc, hzH, ht, hout, hconj, he, hF, hsplit, hcard, hself⟩ :=
    large_core_index_two_outside_centralizer_of_inside_fusion hns S hno W hunique hH hindex hinside
  exact houter z t hz hzc hzH ht hout hconj he hF hsplit hcard hself

/-- An extraspecial core of order thirty-two cannot have index two under the
normal-only elementary bound. This covers both extraspecial types and allows
arbitrary elementary eights in the Sylow subgroup. -/
public theorem large_core_index_two_false
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (_hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (_hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) : False := by
  have hinside := large_core_index_two_inside_fusion hN S hZ hno W hW hunique hH hindex
  obtain ⟨z, t, hz, hzc, _, _, hconj, he, hE, hsat⟩ :=
    large_core_index_two_saturated_elementary_centralizer
      hns S hno W hunique hH hindex hinside
  let E := centralizer ({t} : Set S)
  let : IsElementaryAbelian 2 E := he
  let U := E.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hU : Nat.card U = 8 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective]
    exact hE
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hU
    contradiction
  exact S.false_of_saturated_elementary_eight_centralizer z t hzc hz hconj E rfl hE
    (hN _ ⟨U, hUne, IsElementaryAbelian.isPGroup 2 U, rfl⟩) hsat
    (large_core_index_two_normalizer_card S hno hH hindex)

end Stellmacher.Recognition.NormalEightNonnormalImage
