module
public import Theory.Representation.PSL3Two.SingerRestriction

/-!
# Coprime Singer polynomials on the two marked binary pairs

For the fixed symmetric Singer matrix, t³+t²+1 annihilates the natural
module and t³+t+1 annihilates the dual. Each opposite polynomial is
bijective. The statements retain the actual matrix and doubled actions,
so polynomial words can be applied to original group sections.
-/

public noncomputable section
namespace BinaryLinearThree.SingerPairPolynomials
open Matrix.PSL3Two.OuterInvolutionSinger

private theorem natural_zero (v : Vector) : W (singer^3) v+W (singer^2) v+v=0 :=
  (by decide : ∀ v : Vector, W (singer^3) v+W (singer^2) v+v=0) v

private theorem natural_injective_zero (v : Vector) : W (singer^3) v+W singer v+v=0 → v=0 :=
  (by decide : ∀ v : Vector, W (singer^3) v+W singer v+v=0 → v=0) v

private theorem dual_zero (v : Module.Dual (ZMod 2) Vector) :
    W.dual (singer^3) v+W.dual singer v+v=0 := by
  apply LinearMap.ext
  intro w
  change v (W ((singer^3)⁻¹) w)+v (W (singer⁻¹) w)+v w=0
  rw [←map_add,←map_add]
  have hw : W ((singer^3)⁻¹) w+W (singer⁻¹) w+w=0 :=
    (by decide : ∀ w : Vector, W ((singer^3)⁻¹) w+W (singer⁻¹) w+w=0) w
  rw [hw,map_zero]

private theorem dual_injective_zero (v : Module.Dual (ZMod 2) Vector) :
    W.dual (singer^3) v+W.dual (singer^2) v+v=0 → v=0 := by
  intro hv
  have hi : Function.Surjective (fun w : Vector => W ((singer^3)⁻¹) w+W ((singer^2)⁻¹) w+w) := by decide
  apply LinearMap.ext
  intro w
  obtain ⟨x,hx⟩ := hi w
  rw [←hx]
  have hh := LinearMap.congr_fun hv x
  change v (W ((singer^3)⁻¹) x)+v (W ((singer^2)⁻¹) x)+v x=0 at hh
  simpa only [map_add,LinearMap.zero_apply,add_zero] using hh

private theorem linear_bijective {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (f : X →ₗ[ZMod 2] X) (hf : ∀ x, f x=0 → x=0) : Function.Bijective f := by
  have hi : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hf
    rw [map_sub,hxy,sub_self]
  exact ⟨hi,Finite.injective_iff_surjective.mp hi⟩

/-- Natural pairs are annihilated by t³+t²+1, while t³+t+1 is bijective. -/
theorem natural_pair :
    (∀ v : Vector × Vector,
      (W.prod W) (singer^3) v+(W.prod W) (singer^2) v+v=0) ∧
    Function.Bijective (fun v : Vector × Vector =>
      (W.prod W) (singer^3) v+(W.prod W) singer v+v) := by
  constructor
  · intro v
    exact Prod.ext (natural_zero v.1) (natural_zero v.2)
  · let f : (Vector × Vector) →ₗ[ZMod 2] (Vector × Vector) :=
      (W.prod W) (singer^3)+(W.prod W) singer+LinearMap.id
    have hh : Function.Bijective f := linear_bijective f (by
      intro v hv
      exact Prod.ext (natural_injective_zero v.1 (congrArg Prod.fst hv))
        (natural_injective_zero v.2 (congrArg Prod.snd hv)))
    change Function.Bijective (fun v => f v) at hh
    simpa only [f,LinearMap.add_apply,LinearMap.id_apply] using hh

/-- Dual pairs are annihilated by t³+t+1, while t³+t²+1 is bijective. -/
theorem dual_pair :
    (∀ v : Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector,
      (W.dual.prod W.dual) (singer^3) v+(W.dual.prod W.dual) singer v+v=0) ∧
    Function.Bijective (fun v : Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector =>
      (W.dual.prod W.dual) (singer^3) v+(W.dual.prod W.dual) (singer^2) v+v) := by
  let : Finite (Module.Dual (ZMod 2) Vector) := Module.finite_of_finite (ZMod 2)
  constructor
  · intro v
    exact Prod.ext (dual_zero v.1) (dual_zero v.2)
  · let f : (Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector) →ₗ[ZMod 2]
        (Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector) :=
      (W.dual.prod W.dual) (singer^3)+(W.dual.prod W.dual) (singer^2)+LinearMap.id
    have hh : Function.Bijective f := linear_bijective f (by
      intro v hv
      exact Prod.ext (dual_injective_zero v.1 (congrArg Prod.fst hv))
        (dual_injective_zero v.2 (congrArg Prod.snd hv)))
    change Function.Bijective (fun v => f v) at hh
    simpa only [f,LinearMap.add_apply,LinearMap.id_apply] using hh

end BinaryLinearThree.SingerPairPolynomials
