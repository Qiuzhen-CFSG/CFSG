module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Binary conjugation coordinates and their literal kernels

A multiplicative marking of a subgroup as a binary vector space transports
its full normalizer action to a linear representation. An equivariant
marking through any faithful model identifies the model-action kernel with
the actual centralizer, and its image order with the relative index.

These are the conjugation and quotient transports used in the terminal
argument of Aschbacher–Smith 13.4.1, printed p.915.
-/

public noncomputable section
open Subgroup
namespace BinaryConjugationCoordinates
variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
/-- The actual full normalizer action in the prescribed binary coordinates. -/
def action (W : Subgroup G) (e : W ≃* Multiplicative X) :
    Representation (ZMod 2) (normalizer (W : Set G)) X where
  toFun g :=
    ({ toFun v := (e (W.normalizerMonoidHom g (e.symm (Multiplicative.ofAdd v)))).toAdd
       map_zero' := by simp
       map_add' v w := by
         change (e (W.normalizerMonoidHom g (e.symm
           (Multiplicative.ofAdd v * Multiplicative.ofAdd w)))).toAdd = _
         rw [map_mul,map_mul,map_mul]
         rfl } : X →+ X).toZModLinearMap 2
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp
/-- Evaluating the coordinate action on a marked group element. -/
@[simp] theorem action_apply (W : Subgroup G) (e : W ≃* Multiplicative X)
    (g : normalizer (W : Set G)) (w : W) :
    action W e g (e w).toAdd = (e (W.normalizerMonoidHom g w)).toAdd := by
  change (e (W.normalizerMonoidHom g (e.symm (e w)))).toAdd = _
  rw [e.symm_apply_apply]
variable {Q : Type*} [Group Q]

/-- Faithfulness identifies the model kernel with the literal group centralizer. -/
theorem model_kernel
    (A W : Subgroup G) (hAW : A ≤ normalizer (W : Set G))
    (ρ : Representation (ZMod 2) Q X) (hρ : Function.Injective ρ)
    (φ : A →* Q)
    (e : W ≃* Multiplicative X)
    (he : ∀ (a : A) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        ρ (φ a) (e w).toAdd) :
    φ.ker = (centralizer (W : Set G)).subgroupOf A := by
  ext a
  change φ a = 1 ↔ a.val ∈ centralizer (W : Set G)
  constructor
  · intro ha
    apply mem_centralizer_iff.mpr
    intro w hw
    have hh := he a ⟨w,hw⟩
    rw [ha,map_one,Module.End.one_apply] at hh
    have hc := congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective hh))
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro ha
    apply hρ
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := e.surjective (Multiplicative.ofAdd v)
    have hw' : (e w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [← hw']
    have hc : W.normalizerMonoidHom ⟨a.val,hAW a.property⟩ w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp ha w.val w.property).symm)
    rw [← he,hc,map_one,Module.End.one_apply]

/-- The model image has the actual centralizer index, without changing the actor. -/
theorem model_card_range
    (A W : Subgroup G) (hAW : A ≤ normalizer (W : Set G))
    (ρ : Representation (ZMod 2) Q X) (hρ : Function.Injective ρ)
    (φ : A →* Q)
    (e : W ≃* Multiplicative X)
    (he : ∀ (a : A) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        ρ (φ a) (e w).toAdd) :
    Nat.card φ.range = (A ⊓ centralizer (W : Set G)).relIndex A := by
  rw [← index_ker,model_kernel A W hAW ρ hρ φ e he]
  change (centralizer (W : Set G)).relIndex A = _
  rw [inf_comm,inf_relIndex_right]

end BinaryConjugationCoordinates
