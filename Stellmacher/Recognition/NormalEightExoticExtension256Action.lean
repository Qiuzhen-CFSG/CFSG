module

public import Stellmacher.Recognition.NormalEightExoticExtension256ActionSetup

/-!
# Assembly of the action frame from normalized base actions

Conjugation on the self-centralizing C₄-square has order sixteen. Once its
two prescribed inner actions occur in the elementary sixteen, and swap occurs
in the full image, inversion also occurs there and we choose preimages. The
inner preimages commute and square to one because they belong to the elementary subgroup.
The sixteen-word certificate proves generation modulo the base, and the two
coordinate generators then give generation of the whole group.

The normalization of the inner image and existence of the swap action
remain separate recognition obligations. This assembly does not require any
relations on the outer lifts. Source: Janko–Thompson, Math. Z. 113 (1970),
1.4(c), printed p.386, applied on p.395.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticExtension256

open C4SquareExtension ExoticTwoGroup.ActionModel

/-- Construct the complete action frame from membership of the two inner model
actions and swap. Inversion belongs to every action image of order sixteen.
In particular, generation and the marked omega four need no further recognition
assumptions. -/
public theorem exists_actionFrame_of_model_actions
    {P : Type*} [Group P] [Finite P] (D W B : Subgroup P)
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* Model) (hcard : Nat.card P = 256)
    (h₁ : inner₁ ∈ ((modelAction D e).comp B.subtype).range)
    (h₂ : inner₂ ∈ ((modelAction D e).comp B.subtype).range)
    (ht : swap ∈ (modelAction D e).range) :
    Nonempty (ExoticTwoGroup.ActionFrame D W B) := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  obtain ⟨t, ht⟩ := ht
  obtain ⟨z₀, hz⟩ := inversion_mem_of_card_sixteen (modelAction D e).range
    (card_modelAction_range D hDC e hcard)
  let f : Model →* P := D.subtype.comp e.symm.toMonoidHom
  let a := f u
  let b := f v
  have hr : f.range = D := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  have hbase : D = closure ({a, b} : Set P) := by
    have hh := congrArg (Subgroup.map f) basis
    rw [← MonoidHom.range_eq_map, hr] at hh
    simpa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, a, b]
      using hh.symm
  have hfour : W = closure ({a ^ 2, b ^ 2} : Set P) := by
    rw [← hDO]
    change (omega D (p := 2) 1).map D.subtype = _
    rw [← e.symm.map_omega 2 1, Subgroup.map_map]
    change (omega₁ Model (p := 2)).map f = _
    rw [omega_basis]
    simp [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, a, b]
  have hc (x : P) (α : MulAut Model) (hx : modelAction D e x = α) (y : Model) :
      x * f y * x⁻¹ = f (α y) := by
    have hh := congrArg (fun β : MulAut Model => e.symm (β y)) hx
    change e.symm (e (MulAut.conjNormal x (e.symm y))) = e.symm (α y) at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Subtype.val hh
  let J := closure ({a, b, (g₁ : P), (g₂ : P), t, z₀} : Set P)
  have hDJ : D ≤ J := by
    rw [hbase]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hg₁J : (g₁ : P) ∈ J := subset_closure (by simp)
  have hg₂J : (g₂ : P) ∈ J := subset_closure (by simp)
  have htJ : t ∈ J := subset_closure (by simp)
  have hzJ : z₀ ∈ J := subset_closure (by simp)
  have hmap : J.map (modelAction D e) = (modelAction D e).range := by
    apply eq_of_le_of_card_ge (map_le_range _ _)
    rw [card_modelAction_range D hDC e hcard]
    apply sixteen_le_card
    · exact ⟨g₁, hg₁J, hg₁⟩
    · exact ⟨g₂, hg₂J, hg₂⟩
    · exact ⟨t, htJ, ht⟩
    · exact ⟨z₀, hzJ, hz⟩
  have hgen : J = ⊤ := by
    apply top_unique
    intro x _
    have hx : modelAction D e x ∈ J.map (modelAction D e) := by
      rw [hmap]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy, heq⟩ := hx
    have hker : y⁻¹ * x ∈ (modelAction D e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    rw [modelAction_ker D hDC e] at hker
    simpa using J.mul_mem hy (hDJ hker)
  refine ⟨{
    a := a, b := b, g₁ := g₁, g₂ := g₂, t := t, z₀ := z₀
    a_four := ?_, b_four := ?_, ab := (Commute.all u v).map f
    base := hbase, four := hfour
    g₁_mem := g₁.property, g₂_mem := g₂.property
    g₁_two := elemPow_eq_one_of_isElementaryAbelian _ g₁.property
    g₂_two := elemPow_eq_one_of_isElementaryAbelian _ g₂.property
    g₁g₂ := (show Commute g₁ g₂ from IsMulCommutative.is_comm.comm g₁ g₂).map B.subtype
    g₁_a := ?_, g₁_b := ?_, g₂_a := ?_, g₂_b := ?_
    z₀_a := ?_, z₀_b := ?_, t_a := ?_, t_b := ?_, generate := hgen }⟩
  · change (f u) ^ 4 = 1
    rw [← map_pow, u_four, map_one]
  · change (f v) ^ 4 = 1
    rw [← map_pow, v_four, map_one]
  · simpa only [inner₁_u, map_inv] using hc g₁ inner₁ hg₁ u
  · simpa only [inner₁_v, map_mul, map_pow, map_inv] using hc g₁ inner₁ hg₁ v
  · simpa only [inner₂_u, map_mul, map_pow, map_inv] using hc g₂ inner₂ hg₂ u
  · simpa only [inner₂_v, map_inv] using hc g₂ inner₂ hg₂ v
  · simpa only [inversion_u, map_inv] using hc z₀ inversion hz u
  · simpa only [inversion_v, map_inv] using hc z₀ inversion hz v
  · simpa only [swap_u] using hc t swap ht u
  · simpa only [swap_v] using hc t swap ht v

end Stellmacher.Recognition.NormalEightExoticExtension256
