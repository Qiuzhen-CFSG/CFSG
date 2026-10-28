module
public import Theory.LinearAlgebra.AlternatingRankTwoCoordinates
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Coordinates for a ternary alternating pairing of rank two

An elementary group of order81 is a four-dimensional ternary vector space.
An alternating pairing into the fixed multiplicative ternary field, with
radical of order9, therefore has a normalized rank-two coordinate form.
The proof converts the actual pairing to a bilinear form and applies the
radical-complement construction, retaining the given scalar map.

The original marked-core application is the quotient comparison in
Aschbacher–Smith I.4.5, printed p.417; see `AtlasFormCoordinates`.
-/

@[expose] public section
open scoped IsMulCommutative
namespace IsElementaryAbelian
variable {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 3 V]

private def ternaryPairingAdd (b : V →* (V →* Multiplicative (ZMod 3))) :
    Additive V →+ (Additive V →+ ZMod 3) where
  toFun x := (b x.toMul).toAdditiveLeft
  map_zero' := by apply AddMonoidHom.ext; intro y; change (b 1 y.toMul).toAdd=0; simp
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    change (b (x.toMul*y.toMul) z.toMul).toAdd =
      (b x.toMul z.toMul).toAdd+(b y.toMul z.toMul).toAdd
    rw [map_mul,MonoidHom.mul_apply]
    rfl

private def ternaryPairingForm (b : V →* (V →* Multiplicative (ZMod 3))) :
    LinearMap.BilinForm (ZMod 3) (Additive V) :=
  ((AddMonoidHom.toZModLinearMapEquiv 3).toAddMonoidHom.comp (ternaryPairingAdd b)).toZModLinearMap 3

/-- An alternating cubic pairing on a group of order81 with radical of order9
has actual rank-two coordinates, preserving its fixed scalar-value map. -/
theorem exists_ternary_alternating_coordinates
    (b : V →* (V →* Multiplicative (ZMod 3))) (halt : ∀ v,b v v=1)
    (R : Subgroup V) (hrad : ∀ v,(∀ w,b v w=1) ↔ v∈R)
    (hV : Nat.card V=81) (hR : Nat.card R=9) :
    ∃ e : V ≃* Multiplicative (Fin 4 → ZMod 3),
      ∀ v w,b v w=Multiplicative.ofAdd
        ((e v).toAdd 0*(e w).toAdd 3-(e w).toAdd 0*(e v).toAdd 3) := by
  let B := ternaryPairingForm b
  have hB : B.IsAlt := by
    intro v
    change (b v.toMul v.toMul).toAdd=0
    rw [halt]
    rfl
  have hk : B.ker = AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup R) := by
    ext v
    change B v=0 ↔ v.toMul∈R
    rw [←hrad]
    constructor
    · intro h w
      exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun h (Additive.ofMul w))
    · intro h
      ext w
      exact congrArg Multiplicative.toAdd (h w.toMul)
  have hd : Module.finrank (ZMod 3) (Additive V)=4 := by
    apply Nat.pow_right_injective (by decide : 2≤3)
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=Additive V)
    exact (hh.trans (by rw [Nat.card_zmod])).symm.trans hV
  have hr : Module.finrank (ZMod 3) B.ker=2 := by
    apply Nat.pow_right_injective (by decide : 2≤3)
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=B.ker)
    have hc : Nat.card B.ker=9 := by rw [hk]; exact hR
    exact (hh.trans (by rw [Nat.card_zmod])).symm.trans hc
  obtain ⟨e,he⟩ := AlternatingForm.exists_four_coordinates B hB hd hr
  refine ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv,?_⟩
  intro v w
  exact congrArg Multiplicative.ofAdd (he (Additive.ofMul v) (Additive.ofMul w))

end IsElementaryAbelian
