module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.FieldTheory.Finiteness

/-!
# The faithful cyclic-four action on an elementary nine

Linearization in a basis of the actual elementary group reduces the square
of an order-four automorphism to an 81-matrix calculation over F₃. Its square
is inversion. The three nonidentity cyclic actors consequently have trivial
fixed subgroup. This is the local action input in Aschbacher, *Sporadic
Groups* (1994), Exercise 2, printed p.249; it applies to the literal Sylow
normalizer action in the source recognition.
-/

@[expose] public section
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI

private theorem matrix_square : ∀A:Matrix (Fin 2) (Fin 2) (ZMod 3),
    A^4=1 → A^2≠1 → A^2= -1 := by decide +kernel

variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]

private def linearAut : MulAut E →* (Additive E ≃ₗ[ZMod 3] Additive E) where
  toFun a := {a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive}
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

private noncomputable def linearEnd : MulAut E →* Module.End (ZMod 3) (Additive E) :=
  {toFun := fun a => (linearAut a).toLinearMap
   map_one' := by ext; rfl
   map_mul' := by intros; ext; rfl}

omit [Finite E] in
private theorem linearEnd_injective : Function.Injective (linearEnd (E:=E)) := by
  intro a b h
  ext x
  exact congrArg Additive.toMul (LinearMap.congr_fun h (Additive.ofMul x))

theorem fourth_power_square_inverts (hE : Nat.card E=9)
    (a:MulAut E) (ha:a^4=1) (ha2:a^2≠1) (x:E) : a (a x)=x⁻¹ := by
  classical
  have hdim : Module.finrank (ZMod 3) (Additive E)=2 := by
    have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=Additive E)
    change Nat.card E = _ at hc
    rw [hE,Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 1<3)) hc.symm
  let b:=Module.finBasisOfFinrankEq (ZMod 3) (Additive E) hdim
  let f:= (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp linearEnd
  have hf:Function.Injective f := (LinearMap.toMatrixAlgEquiv b).injective.comp linearEnd_injective
  have hm:(f a)^2= -1 := matrix_square (f a)
    (by rw [←map_pow,ha,map_one]) (fun h=>ha2 (hf (by simpa only [map_pow,map_one] using h)))
  have he:linearEnd a ^2= -1 := (LinearMap.toMatrixAlgEquiv b).injective (by
    change (LinearMap.toMatrixAlgEquiv b) (linearEnd a)^2 = -1 at hm
    simpa only [map_pow,map_neg,map_one] using hm)
  exact congrArg Additive.toMul (LinearMap.congr_fun he (Additive.ofMul x))

theorem fourth_power_fixed_eq_one (hE:Nat.card E=9)
    (a:MulAut E) (ha:a^4=1) (ha2:a^2≠1) (x:E) (hx:a x=x) : x=1 := by
  have hinv:x=x⁻¹ := by simpa only [hx] using fourth_power_square_inverts hE a ha ha2 x
  have h2:x^2=1 := by rw [pow_two]; nth_rw 1 [hinv]; exact inv_mul_cancel x
  have h3:x^3=1:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 E) x
  have hh:=pow_succ x 2
  rw [h2,h3,one_mul] at hh
  exact hh.symm

theorem cyclic_four_fixed_eq_one (hE:Nat.card E=9)
    (ρ : Multiplicative (ZMod 4) →* MulAut E) (hρ:Function.Injective ρ)
    (c:Multiplicative (ZMod 4)) (hc:c≠1) (x:E) (hx:ρ c x=x) : x=1 := by
  let a:=ρ (Multiplicative.ofAdd (1:ZMod 4))
  have h4:a^4=1 := by
    rw [←map_pow,show (Multiplicative.ofAdd (1:ZMod 4))^4=1 by decide,map_one]
  have h2:a^2≠1 := by
    intro hh
    have he:(Multiplicative.ofAdd (1:ZMod 4))^2=1 := hρ (by simpa only [map_pow,map_one] using hh)
    exact (by decide : (Multiplicative.ofAdd (1:ZMod 4))^2≠1) he
  have hcan:c=Multiplicative.ofAdd c.toAdd:=rfl
  rw [hcan] at hx hc
  generalize c.toAdd = i at hx hc
  fin_cases i
  · exact (hc rfl).elim
  · exact fourth_power_fixed_eq_one hE a h4 h2 x hx
  · have hh:a (a x)=x := by
      change (a^2) x=x
      rw [←map_pow]
      exact hx
    have hi:x=x⁻¹:=hh.symm.trans (fourth_power_square_inverts hE a h4 h2 x)
    have hsq:x^2=1 := by rw [pow_two]; nth_rw 1 [hi]; exact inv_mul_cancel x
    have hcube:x^3=1:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E) x
    have hh:=pow_succ x 2
    rw [hsq,hcube,one_mul] at hh
    exact hh.symm
  · have h3:(a^3) x=x := by rw [←map_pow]; exact hx
    have ha:a x=x := by
      have hh:=congrArg (fun f:MulAut E=>f x) h4
      change (a^4) x=x at hh
      rw [show (4:ℕ)=1+3 by decide,pow_add,MulAut.mul_apply,pow_one,h3] at hh
      exact hh
    exact fourth_power_fixed_eq_one hE a h4 h2 x ha
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
