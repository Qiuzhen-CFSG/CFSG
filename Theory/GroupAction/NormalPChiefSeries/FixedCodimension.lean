module
public import Theory.GroupAction.NormalPChiefSeries.Linear

/-!
# Fixed codimension for the literal normal elementary action

The fixed subspace of conjugation on `Additive U` has the same underlying
set as `C_U(A)`. Comparing their cardinalities identifies the binary fixed
codimension with the difference of the logarithms of the two group orders.
This connects the chief-series equalities in Aschbacher–Smith 15.1.12(2)
with the maximum elementary replacement in its part (4), printed p.1090.
-/

open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
universe u
namespace NoncentralChiefRefinement
variable {H : Type u} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

omit [Finite H] in
private theorem mem_normal_fixedSpace (A : Subgroup H) (v : Additive U) :
    v ∈ fixedSpace (normalRepresentation U) A ↔ (v.toMul : H) ∈ centralizer (A : Set H) := by
  constructor
  · intro hv a ha
    have he := congrArg (fun w : Additive U => (w.toMul : H)) (hv ⟨a, ha⟩)
    change a * (v.toMul : H) * a⁻¹ = v.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : H) * v.toMul * (a : H)⁻¹ = v.toMul
    rw [hv a a.property, mul_inv_cancel_right]

/-- The normal-action fixed codimension is the actual relative centralizer rank. -/
public theorem normalRepresentation_fixedCodim_eq_rank_difference (A : Subgroup H) :
    fixedCodim (normalRepresentation U) A = Nat.log 2 (Nat.card U) -
      Nat.log 2 (Nat.card ↥(U ⊓ centralizer (A : Set H))) := by
  let e : fixedSpace (normalRepresentation U) A ≃ ↥(U ⊓ centralizer (A : Set H)) :=
    { toFun := fun v => ⟨v.val.toMul, v.val.toMul.property,
        (mem_normal_fixedSpace U A v.val).mp v.property⟩
      invFun := fun u => ⟨Additive.ofMul ⟨u, u.property.1⟩,
        (mem_normal_fixedSpace U A _).mpr u.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hlog (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
      Module.finrank (ZMod 2) W = Nat.log 2 (Nat.card W) := by
    have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
      simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hc, Nat.log_pow Nat.one_lt_two]
  rw [fixedCodim, Submodule.finrank_quotient, hlog (Additive ↥U), hlog (fixedSpace (normalRepresentation U) A), Nat.card_congr e]
  rfl
end NoncentralChiefRefinement
