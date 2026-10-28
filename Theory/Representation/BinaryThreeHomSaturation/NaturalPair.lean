module
public import Theory.Representation.BinaryThreeHomSaturation.Groups
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finiteness
/-!
# Natural coordinates on the dual Hom pair

A binary four-group has two independent scalar coordinates. Composing these
with a homomorphism from the dual three-space, then using the dot-product
identification with the double dual, gives two natural three-spaces. The
intertwining formula retains the literal inverse-transpose action.

Source application: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iv), p.899.
-/

@[expose] public section
namespace Representation.BinaryThreeHom
variable {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]
noncomputable def linearPairEquiv (e : T ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2)) :
    (W →ₗ[ZMod 2] T) ≃ₗ[ZMod 2] (W × W) :=
  (LinearEquiv.congrRight e).trans ((LinearMap.prodEquiv (R := ZMod 2) (S := ZMod 2)).symm.trans
    (LinearEquiv.prodCongr (dotProductEquiv (ZMod 2) (Fin 3)).symm
      (dotProductEquiv (ZMod 2) (Fin 3)).symm))

theorem linearPairEquiv_eval (e : T ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2))
    (f : W →ₗ[ZMod 2] T) (v : W) :
    (dotProduct (linearPairEquiv e f).1 v,dotProduct (linearPairEquiv e f).2 v) = e (f v) := by
  apply Prod.ext
  · exact congrArg (fun l : W →ₗ[ZMod 2] ZMod 2 => l v)
      ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply
        ((LinearMap.fst _ _ _).comp (e.toLinearMap.comp f)))
  · exact congrArg (fun l : W →ₗ[ZMod 2] ZMod 2 => l v)
      ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply
        ((LinearMap.snd _ _ _).comp (e.toLinearMap.comp f)))

private theorem dot_dual_inverse (g : S) (w v : W) :
    dotProduct w (dualAction g⁻¹ v) = dotProduct (g.val.mulVec w) v := by
  change dotProduct w (((g⁻¹)⁻¹).val.transpose.mulVec v) = _
  rw [inv_inv, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem linearPairEquiv_action (e : T ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2))
    (f h : W →ₗ[ZMod 2] T) (g : S)
    (ha : ∀ v : W, h (dualAction g v) = f v) :
    linearPairEquiv e h = (g.val.mulVec (linearPairEquiv e f).1,
      g.val.mulVec (linearPairEquiv e f).2) := by
  have he (v : W) : e (h v) = e (f (dualAction g⁻¹ v)) := by
    have hinv : dualAction g (dualAction g⁻¹ v) = v := by
      simpa only [inv_inv] using dualAction_inv_apply (g⁻¹) v
    exact congrArg e ((congrArg h hinv).symm.trans (ha _))
  apply Prod.ext
  · apply (dotProductEquiv (ZMod 2) (Fin 3)).injective
    apply LinearMap.ext
    intro v
    calc
      _ = (e (h v)).1 := congrArg Prod.fst (linearPairEquiv_eval e h v)
      _ = (e (f (dualAction g⁻¹ v))).1 := congrArg Prod.fst (he v)
      _ = dotProduct (linearPairEquiv e f).1 (dualAction g⁻¹ v) :=
        (congrArg Prod.fst (linearPairEquiv_eval e f _)).symm
      _ = _ := dot_dual_inverse g _ v
  · apply (dotProductEquiv (ZMod 2) (Fin 3)).injective
    apply LinearMap.ext
    intro v
    calc
      _ = (e (h v)).2 := congrArg Prod.snd (linearPairEquiv_eval e h v)
      _ = (e (f (dualAction g⁻¹ v))).2 := congrArg Prod.snd (he v)
      _ = dotProduct (linearPairEquiv e f).2 (dualAction g⁻¹ v) :=
        (congrArg Prod.snd (linearPairEquiv_eval e f _)).symm
      _ = _ := dot_dual_inverse g _ v
open scoped IsMulCommutative
variable {H : Type*} [Group H] [IsElementaryAbelian 2 H]

noncomputable def groupPairEquiv (e : Additive H ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2)) :
    (Multiplicative W →* H) ≃* Multiplicative (W × W) :=
  (homEquivLinear (T := H)).trans (linearPairEquiv e).toAddEquiv.toMultiplicative

theorem groupPairEquiv_action (e : Additive H ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2))
    (f h : Multiplicative W →* H) (g : S)
    (ha : ∀ v : W, h (Multiplicative.ofAdd (dualAction g v)) = f (Multiplicative.ofAdd v)) :
    (groupPairEquiv e h).toAdd = (g.val.mulVec (groupPairEquiv e f).toAdd.1,
      g.val.mulVec (groupPairEquiv e f).toAdd.2) := by
  apply linearPairEquiv_action
  intro v
  exact congrArg Additive.ofMul (ha v)

theorem exists_binary_pair_equiv (hH : Nat.card H = 4) :
    Nonempty (Additive H ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2)) := by
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; decide)
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive H)
  change Nat.card H = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive H) at he
  have hd : Module.finrank (ZMod 2) (Additive H) = 2 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    simpa only [Nat.card_zmod, hH] using he.symm
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd] using hd
end Representation.BinaryThreeHom
