module

public import Theory.SpecificGroups.Janko4.Representations.InvolutionDisplacement
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Involution displacement in elementary abelian J₄ actions

A faithful action on an elementary abelian two-group is a faithful binary
representation on its additive form. Every J₄ involution moves at least
twelve dimensions, so a subgroup containing all of its action differences
has at least 4096 elements. The inclusion of the displacement space into
that actual subgroup supplies the cardinal bound.

This is the multiplicative form of the native J₄ displacement theorem,
used in Aschbacher--Smith 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace Janko4.BinaryDegree

theorem involution_moved_subgroup_card
    {X E : Type*} [Group X] [Finite X] [Group E] [Finite E]
    [IsElementaryAbelian 2 E]
    (f : X →* MulAut E) (hf : Function.Injective f) (e : X ≃* Model)
    (t : X) (ht : orderOf t = 2) (B : Subgroup E)
    (hb : ∀ v : E, f t v * v⁻¹ ∈ B) :
    4096 ≤ Nat.card B := by
  let ρ : Representation (ZMod 2) X (Additive E) := {
    toFun a := { (f a).toAdditive.toAddMonoidHom with
      map_smul' := ZMod.map_smul (f a).toAdditive.toAddMonoidHom }
    map_one' := by
      apply LinearMap.ext
      intro v
      change f 1 v.toMul = v.toMul
      rw [f.map_one]
      rfl
    map_mul' a b := by
      apply LinearMap.ext
      intro v
      change f (a * b) v.toMul = f a (f b v.toMul)
      exact congrArg (fun a : MulAut E => a v.toMul) (f.map_mul a b) }
  have hρ : Function.Injective ρ := by
    intro x y he
    apply hf
    ext v
    exact congrArg (fun a : Module.End (ZMod 2) (Additive E) =>
      (a (Additive.ofMul v)).toMul) he
  have hl := twelve_le_fixedCodim_of_involution ρ hρ e t ht
  rw [fixedCodim_zpowers_eq_displacement_rank] at hl
  have hmem : ∀ y ∈ LinearMap.range (ρ t - LinearMap.id), y.toMul ∈ B := by
    rintro y ⟨x,rfl⟩
    change f t x.toMul / x.toMul ∈ B
    simpa only [div_eq_mul_inv] using hb x.toMul
  let j : LinearMap.range (ρ t - LinearMap.id) → B := fun y => ⟨y.val.toMul,hmem y y.property⟩
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun b : B => Additive.ofMul b.val) he)
  have hc := Nat.card_le_card_of_injective j hj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact (show 4096 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) from
    Nat.pow_le_pow_right (by decide : 0 < 2) hl).trans hc

end Janko4.BinaryDegree
