module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum

/-!
# The affine group of the cyclic group of order eight

`AffineEight.Model` is the actual semidirect product of the additive group
of the ring Z/8 with its unit group, acting by multiplication. Thus it is
the holomorph of the cyclic group of order eight. The model is built from
these operations and has order32.

`evenEmbedding` embeds C₂ × D₈ as the affine maps with even translation.
The C₂ generator acts by multiplication by5, the dihedral rotation translates
by2, and its reflection acts by multiplication by7. The image has index two
and is exactly the centralizer of the first-factor involution. It is also
the normalizer of the canonical elementary eight subgroup, consisting of
maps whose translation is divisible by4. All these assertions are checked
on the explicit finite arithmetic model.

This supplies the concrete target for the local C₂ × D₈ index-two extension
comparison in the order32 Sylow branch of Kurzweil–Stellmacher, The Theory
of Finite Groups, Chapter12, p367. No arbitrary finite group is identified
with this model here, and no external small-group identifier is used.
-/

namespace AffineEight

@[expose] public def unitAction : (ZMod 8)ˣ →* MulAut (Multiplicative (ZMod 8)) where
  toFun u := {
    toFun x := Multiplicative.ofAdd ((u : ZMod 8) * x.toAdd)
    invFun x := Multiplicative.ofAdd ((↑(u⁻¹) : ZMod 8) * x.toAdd)
    left_inv x := by simp [← mul_assoc]
    right_inv x := by simp [← mul_assoc]
    map_mul' x y := by
      change Multiplicative.ofAdd ((u : ZMod 8) * (x.toAdd + y.toAdd)) = _
      rw [mul_add]
      rfl }
  map_one' := by ext x; simp
  map_mul' u v := by ext x; simp [mul_assoc]

/-- The affine group of the additive cyclic group of order eight. -/
public abbrev Model := Multiplicative (ZMod 8) ⋊[unitAction] (ZMod 8)ˣ

public instance : Fintype Model :=
  Fintype.ofEquiv (Multiplicative (ZMod 8) × (ZMod 8)ˣ) SemidirectProduct.equivProd.symm

@[expose] public def five : (ZMod 8)ˣ := ⟨5, 5, by decide, by decide⟩
@[expose] public def seven : (ZMod 8)ˣ := ⟨7, 7, by decide, by decide⟩

@[expose] public def evenEmbedding :
    Multiplicative (ZMod 2) × DihedralGroup 4 →* Model where
  toFun d := {
    left := Multiplicative.ofAdd (match d.2 with
      | .r j => 2 * (j.val : ZMod 8)
      | .sr j => -(2 * (j.val : ZMod 8)))
    right := five ^ d.1.toAdd.val * match d.2 with
      | .r _ => 1
      | .sr _ => seven }
  map_one' := by decide
  map_mul' := by decide

public theorem evenEmbedding_injective : Function.Injective evenEmbedding := by decide

public theorem card_model : Nat.card Model = 32 := by
  change Nat.card (Multiplicative (ZMod 8) ⋊[unitAction] (ZMod 8)ˣ) = _
  rw [SemidirectProduct.card]
  norm_num [Nat.card_eq_fintype_card]
  decide


@[expose] public def evenElementary : Subgroup Model :=
  (Subgroup.centralizer ({(1, DihedralGroup.sr 0)} :
    Set (Multiplicative (ZMod 2) × DihedralGroup 4))).map evenEmbedding

private instance : DecidablePred (· ∈ evenElementary) := fun x =>
  decidable_of_iff
    (∃ d : Multiplicative (ZMod 2) × DihedralGroup 4,
      d * (1, DihedralGroup.sr 0) = (1, DihedralGroup.sr 0) * d ∧ evenEmbedding d = x)
    (by simp only [evenElementary, Subgroup.mem_map,
      Subgroup.mem_centralizer_singleton_iff])

public theorem evenEmbedding_data :
    evenEmbedding.range.index = 2 ∧
    Subgroup.centralizer
      ({evenEmbedding (Multiplicative.ofAdd 1, 1)} : Set Model) = evenEmbedding.range ∧
    Subgroup.normalizer (evenElementary : Set Model) = evenEmbedding.range := by
  have hcard : Nat.card evenEmbedding.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective evenEmbedding_injective).toEquiv,
      Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  refine ⟨?_, ?_, ?_⟩
  · have h := evenEmbedding.range.card_mul_index
    rw [hcard, card_model] at h
    omega
  · have hf : ∀ x : Model,
        x * evenEmbedding (Multiplicative.ofAdd 1, 1) =
          evenEmbedding (Multiplicative.ofAdd 1, 1) * x ↔
        ∃ d, evenEmbedding d = x := by decide
    ext x
    simpa only [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range] using hf x
  · have hf : ∀ x : Model,
        (∀ y : Model, y ∈ evenElementary ↔ x * y * x⁻¹ ∈ evenElementary) ↔
        ∃ d, evenEmbedding d = x := by decide
    ext x
    simpa only [Subgroup.mem_normalizer_iff, MonoidHom.mem_range] using hf x


public theorem mem_evenEmbedding_range_iff (x : Model) :
    x ∈ evenEmbedding.range ↔ x.left.toAdd.val % 2 = 0 := by
  have h : ∀ x : Model, (∃ d, evenEmbedding d = x) ↔ x.left.toAdd.val % 2 = 0 := by
    decide
  exact h x

public theorem mem_evenElementary_iff (x : Model) :
    x ∈ evenElementary ↔ x.left.toAdd.val % 4 = 0 := by
  have h : ∀ x : Model, x ∈ evenElementary ↔ x.left.toAdd.val % 4 = 0 := by decide
  exact h x

end AffineEight
