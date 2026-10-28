module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.SpecificGroups.ExoticTwoGroup.Presentation
public import Stellmacher.Recognition.NormalEightExoticAbelianBase
public import Stellmacher.Recognition.NormalEightExoticExtension
public import Stellmacher.Recognition.NormalEightExoticExtension128
public import Stellmacher.Recognition.NormalEightExoticExtension512
public import Stellmacher.Recognition.NormalEightExoticExtension256Action
public import Stellmacher.Recognition.NormalEightExoticExtension256Lifts
public import Stellmacher.Recognition.NormalEightExoticExtension256InnerAction
public import Stellmacher.Recognition.NormalEightExoticExtension256SwapAction
public import Stellmacher.Recognition.NormalEightExoticQuarterTurn
public import Theory.SpecificGroups.ExoticTwoGroup.ActionOrientation

/-!
# The exotic structure in the fused trivial-automizer problem

The normal four extends to a self-centralizing normal abelian subgroup `D`.
Its omega subgroup is exactly the original four, and `D` is a product of two
nontrivial cyclic two-groups. The elementary sixteen intersects `D` in that
four; in the one-central-involution case, `D` has index greater than four.

The homocyclic-base and large-base results now supply a base of type
`C₄ × C₄`. The extension order bound and the order-128 and order-512
exclusions force the Sylow subgroup to have order 256. Once coordinates
with the two prescribed inner actions and the outer swap are supplied,
the checked action-frame construction and lift correction give the exact
marked exotic presentation.

The finite action dichotomy supplies oriented coordinates containing swap or
a quarter-turn. The split inner extension excludes the quarter-turn, completing
the marked presentation. These reductions follow
Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386, applied on p.395;
the coordinate and quarter-turn branches occur in MacWilliams, Trans. AMS
150 (1970), §4 (xiv), (xx)–(xxii), printed pp.393 and 399.
-/

namespace Stellmacher.Recognition.NormalEightExoticInnerStructure

open Subgroup

/-- The intrinsic base available to the fused trivial-automizer analysis.
No fusion or normalizer hypothesis is needed for this reduction. -/
public theorem exists_rank_two_base
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧ B ⊓ D = W ∧ 4 < D.index ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hO, hsplit⟩ :=
    S.isPGroup'.exists_normal_abelian_base_of_no_normal_eight hno W hW
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  exact ⟨D, hWD, hDn, hDa, hDC, hO,
    elementary_inf_eq_of_omega_one_eq_four W D B hO hWB,
    four_lt_index_of_normal_abelian_of_elementary_sixteen hZ hno B hB D, hsplit⟩

/-- The fused trivial-automizer configuration has order 256 and admits a
self-centralizing normal C₄-square with the specified omega four. -/
public theorem card_eq_256_and_exists_c4_square_base
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nat.card S = 256 ∧
      ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
        centralizer (D : Set S) ≤ D ∧ (omega₁ D (p := 2)).map D.subtype = W ∧
        Nonempty (D ≃* C4SquareExtension.Model) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hDO, hmodel⟩ :=
    NormalEightExoticAbelianBase.exists_c4_square_base
      hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hcard : Nat.card S = 256 := by
    rcases NormalEightExoticExtension.extension_order_cases S hZ hno B hB D hDC hmodel
      with h128 | h256 | h512
    · exact (NormalEightExoticExtension128.false_of_card_eq_128
        hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
        D hWD hDC hDO hmodel h128).elim
    · exact h256
    · exact (NormalEightExoticExtension512.false_of_card_eq_512_intrinsic
        S hno W D hW hDC hDO hmodel h512).elim
  exact ⟨hcard, D, hWD, hDn, hDa, hDC, hDO, hmodel⟩

/-- The central omega of order two forces nontrivial action on the base
involutions. This excludes the full congruence kernel in the finite action
classification. -/
public theorem model_action_moves_square_one {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup S) [D.Normal] (hWD : W ≤ D)
    (e : D ≃* C4SquareExtension.Model) :
    ∃ f ∈ (NormalEightExoticExtension256.modelAction D e).range,
      ∃ x : C4SquareExtension.Model, x ^ 2 = 1 ∧ f x ≠ x := by
  by_contra! hfix
  have hC : centralizer (W : Set S) = ⊤ := by
    apply top_unique
    intro g _ w hw
    let d : D := ⟨w, hWD hw⟩
    have hd : d ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw)
    have he := hfix (NormalEightExoticExtension256.modelAction D e g)
      ⟨g, rfl⟩ (e d) (by rw [← map_pow, hd, map_one])
    change e (MulAut.conjNormal (H := D) g (e.symm (e d))) = e d at he
    rw [e.symm_apply_apply] at he
    have hh := congrArg Subtype.val (e.injective he)
    change g * w * g⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hi := NormalFourCentralOmegaTwo.centralizer_index_two S hZ W hW
  rw [hC, index_top] at hi
  norm_num at hi

/-- Oriented action coordinates are the sole remaining input to the exact
presentation: the frame construction supplies generation and the marked four,
and ambient fusion supplies every lift relation. -/
public theorem presentation_of_oriented_model_actions
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hcard : Nat.card S = 256)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (D B : Subgroup S) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hWD : W ≤ D) (hWB : W ≤ B) (hDC : centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* C4SquareExtension.Model)
    (h₁ : ExoticTwoGroup.ActionModel.inner₁ ∈
      ((NormalEightExoticExtension256.modelAction D e).comp B.subtype).range)
    (h₂ : ExoticTwoGroup.ActionModel.inner₂ ∈
      ((NormalEightExoticExtension256.modelAction D e).comp B.subtype).range)
    (ht : ExoticTwoGroup.ActionModel.swap ∈
      (NormalEightExoticExtension256.modelAction D e).range) :
    ∃ d : ExoticTwoGroup.Presentation S,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set S) := by
  obtain ⟨f⟩ := NormalEightExoticExtension256.exists_actionFrame_of_model_actions
    D W B hDC hDO e hcard h₁ h₂ ht
  exact NormalEightExoticExtension256.exists_presentation_of_ambient
    S hcard hZ hno W hW hunique hfused D B hWD hWB hDC hDO ⟨e⟩ f

/-- The fused trivial-automizer configuration has the marked exotic
presentation of Janko–Thompson 1.4(c). -/
public theorem exists_presentation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ∃ d : ExoticTwoGroup.Presentation S,
      W = closure ({d.a ^ 2, d.b ^ 2} : Set S) := by
  obtain ⟨hcard, D, hWD, hDn, hDa, hDC, hDO, hmodel⟩ :=
    card_eq_256_and_exists_c4_square_base
      hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  obtain ⟨e, h₁, h₂⟩ := NormalEightExoticExtension256.exists_model_inner_actions
    hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm
    D hWD hDC hDO hmodel hcard
  let F := NormalEightExoticExtension256.modelAction D e
  have hHA : (F.comp B.subtype).range ≤ F.range := by
    rintro f ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  have hH : Nat.card (F.comp B.subtype).range = 4 := by
    change Nat.card (((MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : S →* MulAut D).comp B.subtype)).range) = 4
    rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
    exact card_conj_image_four_of_elementary_sixteen W D B hW hB hDC hDO hWB
  obtain ⟨c, hc₁, hc₂, hc⟩ := ExoticTwoGroup.ActionModel.exists_oriented_action
    (F.comp B.subtype).range F.range hHA hH
    (NormalEightExoticExtension256.card_modelAction_range D hDC e hcard) h₁ h₂
    (model_action_moves_square_one S hZ W hW D hWD e)
  have he₁ : ExoticTwoGroup.ActionModel.inner₁ ∈
      ((NormalEightExoticExtension256.modelAction D (e.trans c)).comp B.subtype).range := by
    rw [NormalEightExoticExtension256.modelAction_trans,
      MonoidHom.comp_assoc, MonoidHom.range_comp]
    exact hc₁
  have he₂ : ExoticTwoGroup.ActionModel.inner₂ ∈
      ((NormalEightExoticExtension256.modelAction D (e.trans c)).comp B.subtype).range := by
    rw [NormalEightExoticExtension256.modelAction_trans,
      MonoidHom.comp_assoc, MonoidHom.range_comp]
    exact hc₂
  rcases hc with hswap | ⟨q, hq, hqu, hqv⟩
  · apply presentation_of_oriented_model_actions S hcard hZ hno W hW hunique hfused
      D B hWD hWB hDC hDO (e.trans c) he₁ he₂
    rw [NormalEightExoticExtension256.modelAction_trans, MonoidHom.range_comp]
    exact hswap
  · have hq' : q ∈ (NormalEightExoticExtension256.modelAction D (e.trans c)).range := by
      rw [NormalEightExoticExtension256.modelAction_trans, MonoidHom.range_comp]
      exact hq
    obtain ⟨t, rfl⟩ := hq'
    exact (NormalEightExoticExtension256.no_quarter_turn
      hns hN S hnonab hcard hZ hno W hW hunique hfused B hB hWB hnorm
      D hWD hDC hDO (e.trans c) he₁ he₂ t hqu hqv).elim

end Stellmacher.Recognition.NormalEightExoticInnerStructure
