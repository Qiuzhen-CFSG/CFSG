module

public import Stellmacher.Recognition.NormalEightExoticExtension256ActionSetup
public import Stellmacher.Recognition.NormalEightExoticExtension256FixedPoints
public import Stellmacher.Recognition.NormalEightExoticExtension256InvertedRoots
public import Theory.SpecificGroups.ExoticTwoGroup.InnerActionRecognition

/-!
# Reduction of inner-action normalization to fixed and inverted elements

The elementary sixteen fixes the omega four and acts on its self-centralizing
C₄-square base with image of order four. The finite recognition lemma then
identifies this image with the prescribed inner four provided every element
outside the base fixes only square-trivial base elements and inverts a base
element of order four. This module transports those two structural premises;
their derivation from the ambient simple-group hypotheses remains separate.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386,
applied on p.395.
-/

open Subgroup C4SquareExtension
namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- The elementary overgroup of the omega four fixes all square-trivial
base elements in every coordinate system. -/
public theorem modelAction_fixed_of_square_eq_one
    {P : Type*} [Group P] (W D B : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 B]
    (hDO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (e : D ≃* Model) (b : B) (x : Model) (hx : x ^ 2 = 1) :
    modelAction D e b x = x := by
  let d := e.symm x
  have hd : d ^ 2 = 1 := by dsimp [d]; rw [← map_pow, hx, map_one]
  have hdW : (d : P) ∈ W := by
    rw [← hDO]
    exact ⟨d, subset_closure (by simpa using hd), rfl⟩
  have hc : (b : P) * (d : P) = (d : P) * (b : P) := by
    exact congrArg Subtype.val ((@IsMulCommutative.is_comm B _ _).comm
      b (⟨d, hWB hdW⟩ : B))
  change e (MulAut.conjNormal (H := D) (b : P) d) = x
  have he : MulAut.conjNormal (H := D) (b : P) d = d := by
    apply Subtype.ext
    change (b : P) * (d : P) * (b : P)⁻¹ = d
    rw [hc, mul_inv_cancel_right]
  rw [he]
  exact e.apply_symm_apply x

/-- Fixed and inverted base elements suffice for inner-action normalization.
The two premises are intrinsic and independent of the chosen coordinates. -/
public theorem inner_mem_of_fixed_and_inverted
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D]
    [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16)
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (e : D ≃* Model)
    (hfixed : ∀ b ∈ B, b ∉ D → ∀ d ∈ D, Commute b d → d ^ 2 = 1)
    (hinverted : ∀ b ∈ B, b ∉ D →
      ∃ d ∈ D, b * d * b⁻¹ = d⁻¹ ∧ d ^ 2 ≠ 1) :
    ExoticTwoGroup.ActionModel.inner₁ ∈ ((modelAction D e).comp B.subtype).range ∧
    ExoticTwoGroup.ActionModel.inner₂ ∈ ((modelAction D e).comp B.subtype).range := by
  let H := ((modelAction D e).comp B.subtype).range
  have hH : Nat.card H = 4 := by
    change Nat.card (((MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : P →* MulAut D).comp B.subtype)).range) = 4
    rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
    exact card_conj_image_four_of_elementary_sixteen W D B hW hB hDC hDO hWB
  have outside (b : B) (hb : modelAction D e b ≠ 1) : (b : P) ∉ D := by
    intro h
    apply hb
    apply MonoidHom.mem_ker.mp
    rwa [modelAction_ker D hDC e]
  apply ExoticTwoGroup.ActionModel.InnerRecognition.inner_mem_of_fixed_and_inverted H hH
  · rintro f ⟨b, rfl⟩ x hx
    exact modelAction_fixed_of_square_eq_one W D B hDO hWB e b x hx
  · rintro f ⟨b, rfl⟩ hf x hx
    let d := e.symm x
    have he : MulAut.conjNormal (H := D) (b : P) d = d := by
      apply e.injective
      exact hx.trans (e.apply_symm_apply x).symm
    have hd : Commute (b : P) (d : P) := by
      have hh := congrArg Subtype.val he
      change (b : P) * (d : P) * (b : P)⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh)
    have hs : d ^ 2 = 1 := Subtype.ext (hfixed b b.property (outside b hf) d d.property hd)
    have hh := congrArg e hs
    simpa only [map_pow, map_one, d, e.apply_symm_apply] using hh
  · rintro f ⟨b, rfl⟩ hf
    obtain ⟨d, hd, hi, hn⟩ := hinverted b b.property (outside b hf)
    let d' : D := ⟨d, hd⟩
    refine ⟨e d', ?_, ?_⟩
    · change e (MulAut.conjNormal (H := D) (b : P) (e.symm (e d'))) = (e d')⁻¹
      rw [e.symm_apply_apply, ← map_inv]
      exact congrArg e (Subtype.ext hi)
    · intro h
      have hh : d' ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using h)
      exact hn (congrArg Subtype.val hh)

/-- The prescribed inner four occurs in the elementary sixteen for the
order-256 exotic extension. -/
public theorem exists_model_inner_actions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [ (Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal ]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B]
    (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hnorm : Subgroup.normalizer (S : Set G) =
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G))
    (D : Subgroup S) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : Subgroup.centralizer (D : Set S) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* C4SquareExtension.Model))
    (hcard : Nat.card S = 256) :
    ∃ e : D ≃* C4SquareExtension.Model,
      ExoticTwoGroup.ActionModel.inner₁ ∈
        ((modelAction D e).comp B.subtype).range ∧
      ExoticTwoGroup.ActionModel.inner₂ ∈
        ((modelAction D e).comp B.subtype).range := by
  obtain ⟨e⟩ := hmodel
  have hfixed := fixed_square_eq_one_of_nontrivial_elementary_action
    hns hN S hnonab hZ hno W hW hunique hfused B hB hWB hnorm D hWD hDC
      hDO ⟨e⟩ hcard
  have hinverted := inverted_roots_of_elementary_sixteen hno W D B hW hWB
    hDC hDO ⟨e⟩ hcard
  exact ⟨e, inner_mem_of_fixed_and_inverted W D B hW hB hDC hDO
    hWB e hfixed hinverted⟩

end Stellmacher.Recognition.NormalEightExoticExtension256
