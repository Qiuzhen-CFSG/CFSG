module
public import Theory.Representation.PSL3Two.FourNaturalRank
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# Inner automorphisms on four equal natural binary three-spaces

A map from four natural SL₃(2) copies to the dual vanishes on each
coordinate. An operator implementing an outer automorphism would turn a
coordinate projection into a surjection to the dual, a contradiction.
Thus the entire linear normalizer acts innerly on the marked component;
its multiplicity action is retained and need not be trivial.

The original constrained point action uses this in
CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNatural.
Source: Aschbacher--Smith 10.1.1(6) and10.2.9, pp.741,751--752.
-/

public noncomputable section
open Subgroup Representation
namespace BinaryLinearThree.FourNatural

private def coordinateIn (i : Fin 4) : W.IntertwiningMap action where
  toLinearMap := LinearMap.single (ZMod 2) (fun _ : Fin 4 => Vector) i
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext j
    by_cases h : i = j
    · subst j
      simp [action]
    · simp [action, Ne.symm h]

/-- Four equal natural copies have no dual quotient. -/
theorem dual_map_eq_zero (f : action.IntertwiningMap W.dual) : f = 0 := by
  have hz (i : Fin 4) : f.comp (coordinateIn i) = 0 :=
    NaturalDual.natural_dual_zero _
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change f v = 0
  have he : v = ∑ i : Fin 4, Pi.single i (v i) := by
    funext i
    simp only [Finset.sum_apply]
    simp
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact congrArg (fun h : W.IntertwiningMap W.dual => h (v i)) (hz i)

/-- Every automorphism implemented on four natural copies is inner. -/
theorem implemented_automorphism_inner (α : MulAut Group)
    (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g v, f (action g v) = action (α g) (f v)) :
    α ∈ MulAut.innerSubgroup Group := by
  by_contra hn
  let p : action.IntertwiningMap (W.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.proj (0 : Fin 4)).comp f.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      exact congrFun (hf g v) 0 }
  let e := AutomorphismAction.naturalOuterEquiv α hn
  let q := e.toIntertwiningMap.comp p
  have hq : q = 0 := dual_map_eq_zero q
  have hsur : Function.Surjective q := by
    apply e.toLinearEquiv.surjective.comp
    intro v
    exact ⟨f.symm (fun _ => v), congrFun (f.apply_symm_apply (fun _ => v)) 0⟩
  obtain ⟨w,hw⟩ := hsur (LinearMap.proj (0 : Fin 3))
  rw [hq] at hw
  have he := congrArg (fun a : Module.Dual (ZMod 2) Vector => a (fun _ => 1)) hw
  exact zero_ne_one he

/-- The full linear normalizer induces only inner component automorphisms. -/
theorem normalizerAutomorphism_inner (f : Representation.BinaryOffender.linearNormalizer action) :
    normalizerAutomorphism f ∈ MulAut.innerSubgroup Group := by
  exact implemented_automorphism_inner _
    (LinearMap.GeneralLinearGroup.toLinearEquiv f.val)
    (normalizerAutomorphism_intertwines f)

end BinaryLinearThree.FourNatural
