module
public import Theory.Representation.PSL3Two.HomogeneousDouble
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Opposing group sections of a homogeneous binary module

A multiplicative central quotient can be compared with a doubled module
without choosing an additive structure on the quotient itself. Its actual
natural injection and contragredient surjection become nonzero intertwiners
in binary coordinates. The homogeneous-double obstruction then applies,
retaining the common actor on the two opposing sections.

This is the transport step for the residual core in Aschbacher--Smith
15.3.24, printed pp.1129--1130.
-/

@[expose] public noncomputable section
open Representation
namespace BinaryLinearThree.HomogeneousDouble
variable {D V X C : Type*} [_root_.Group D] [_root_.Group C]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup X] [Module (ZMod 2) X]

/-- A homogeneous irreducible double cannot have a natural subgroup and
a dual quotient for one surjective three-dimensional binary actor. -/
theorem no_opposing_group_sections
    (a : D →* BinaryLinear.GL V) (ha : Function.Surjective a)
    (v : V ≃ₗ[ZMod 2] Vector)
    (σ : Representation (ZMod 2) D X) [IsIrreducible σ]
    (act : D →* MulAut C) (E : C ≃* Multiplicative (X × X))
    (hE : ∀ d c, (E (act d c)).toAdd =
      (σ d (E c).toAdd.1, σ d (E c).toAdd.2))
    (i : Multiplicative V →* C) (hi : Function.Injective i)
    (ih : ∀ d w, act d (i w) = i (Multiplicative.ofAdd (a d w.toAdd)))
    (p : C →* Multiplicative (Module.Dual (ZMod 2) V))
    (hp : Function.Surjective p)
    (ph : ∀ d c, (p (act d c)).toAdd = (a d).symm.dualMap (p c).toAdd) : False := by
  let b : D →* Group := ((BinaryLinear.SmallParabolicLevi.linearGroupCongr v).trans
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toMonoidHom.comp a
  have hb : Function.Surjective b :=
    ((BinaryLinear.SmallParabolicLevi.linearGroupCongr v).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).surjective.comp ha
  have hv (d : D) (w : V) : v (a d w) = W (b d) (v w) := by
    change v (a d w) = BinaryLinear.OuterCyclic.slEquivLinear 3
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm
        (BinaryLinear.SmallParabolicLevi.linearGroupCongr v (a d))) (v w)
    rw [MulEquiv.apply_symm_apply, BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
      LinearEquiv.symm_apply_apply]
  let il : V →ₗ[ZMod 2] X × X :=
    (AddMonoidHom.toMultiplicative.symm (E.toMonoidHom.comp i)).toZModLinearMap 2
  let pl : (X × X) →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    (AddMonoidHom.toMultiplicative.symm (p.comp E.symm.toMonoidHom)).toZModLinearMap 2
  let j : Representation.IntertwiningMap (W.comp b) (σ.prod σ) := {
    toLinearMap := il.comp v.symm.toLinearMap
    isIntertwining' := by
      intro d
      apply LinearMap.ext
      intro w
      have he := hE d (i (Multiplicative.ofAdd (v.symm w)))
      rw [ih] at he
      change il (a d (v.symm w)) = _ at he
      change il (v.symm (W (b d) w)) = _
      have hv' : v.symm (W (b d) w) = a d (v.symm w) := by
        apply v.injective
        rw [v.apply_symm_apply, hv, v.apply_symm_apply]
      rw [hv']
      exact he }
  have hj : j ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : Vector)
    have he := congrArg (fun f : Representation.IntertwiningMap (W.comp b) (σ.prod σ) => f w) hz
    have hj0 : il (v.symm w) = 0 := he
    have hmul : E (i (Multiplicative.ofAdd (v.symm w))) = 1 := congrArg Multiplicative.ofAdd hj0
    have hzv : v.symm w = 0 := by
      have hh := hi ((E.map_eq_one_iff.mp hmul).trans (map_one i).symm)
      exact congrArg Multiplicative.toAdd hh
    exact hw (by simpa only [v.apply_symm_apply, map_zero] using congrArg v hzv)
  let q : (σ.prod σ).IntertwiningMap (W.dual.comp b) := {
    toLinearMap := v.symm.dualMap.toLinearMap.comp pl
    isIntertwining' := by
      intro d
      apply LinearMap.ext
      intro w
      have he := hE d (E.symm (Multiplicative.ofAdd w))
      simp only [E.apply_symm_apply] at he
      have he' : E.symm (Multiplicative.ofAdd (σ.prod σ d w)) =
          act d (E.symm (Multiplicative.ofAdd w)) := by
        apply E.injective
        rw [E.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        exact he.symm
      apply LinearMap.ext
      intro z
      change (p (E.symm (Multiplicative.ofAdd (σ.prod σ d w)))).toAdd (v.symm z) =
        (p (E.symm (Multiplicative.ofAdd w))).toAdd (v.symm (W ((b d)⁻¹) z))
      rw [he', ph]
      change (p (E.symm (Multiplicative.ofAdd w))).toAdd ((a d).symm (v.symm z)) = _
      congr 1
      apply v.injective
      rw [v.apply_symm_apply]
      have hai : (a d).symm = a d⁻¹ := by rw [map_inv]; rfl
      rw [hai, hv, v.apply_symm_apply, map_inv] }
  have hq : q ≠ 0 := by
    intro hz
    obtain ⟨f, hf⟩ := exists_ne (0 : Module.Dual (ZMod 2) Vector)
    obtain ⟨g, hg⟩ := v.symm.dualMap.surjective f
    obtain ⟨c, hc⟩ := hp (Multiplicative.ofAdd g)
    have he := congrArg (fun t : (σ.prod σ).IntertwiningMap (W.dual.comp b) =>
      t (E c).toAdd) hz
    change v.symm.dualMap (p (E.symm (E c))).toAdd = 0 at he
    rw [E.symm_apply_apply, hc] at he
    exact hf (hg.symm.trans he)
  exact no_natural_dual_maps σ b hb j hj q hq
end BinaryLinearThree.HomogeneousDouble
