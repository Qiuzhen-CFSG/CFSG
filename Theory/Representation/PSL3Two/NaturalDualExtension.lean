module
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Extending the binary natural and dual actions together

Let a normal subgroup act fully as L₃(2) on a natural three-space and its
specified dual. Every extension preserving the two summands still acts by
mutually dual operators. The full paired action constructs its component
automorphism; an outer automorphism would exchange the summands, contradicting
invertibility. Thus each operator is inner, and the natural action is full.

Source application: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1042.
The literal support-normalizer application is ComponentCriticalPair.SourceActions.
-/

public section
open Subgroup Representation
namespace BinaryLinearThree.NaturalDual
variable {H : Type*} [_root_.Group H]

/-- Extending both marked summands preserves their duality and the full natural image. -/
theorem paired_extension
    (η : Representation (ZMod 2) H Vector)
    (ν : Representation (ZMod 2) H (Module.Dual (ZMod 2) Vector))
    (K : Subgroup H) [K.Normal] (q : K →* Group) (hq : Function.Surjective q)
    (hn : ∀ k : K, η k = W (q k))
    (hd : ∀ k : K, ν k = W.dual (q k)) :
    ∃ f : H →* (Vector ≃ₗ[ZMod 2] Vector), Function.Surjective f ∧
      η = LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f ∧ ν = η.dual := by
  let τ := η.prod ν
  obtain ⟨α,hα,_⟩ := exists_automorphism_marking τ K q hq (by
    intro k
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (hn k) v.1) (LinearMap.congr_fun (hd k) v.2))
  have hin (h : H) : α h ∈ MulAut.innerSubgroup Group := by
    by_contra hout
    let t := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom h)
    have hc (g : Group) (v : Space) : t (action g v) = action (α h g) (t v) := by
      change τ h (action g v) = action (α h g) (τ h v)
      rw [hα]
      exact autAction_covariance (α h) g v
    obtain ⟨v,hv⟩ := exists_ne (0 : Vector)
    have hz : t (v,0) = 0 := Prod.ext ((outer_swaps (α h) t hc hout).1 v) (map_zero (ν h))
    exact hv (congrArg Prod.fst (t.injective (hz.trans t.map_zero.symm)))
  have he (h : H) : ∃ g : Group, η h = W g ∧ ν h = W.dual g := by
    obtain ⟨g,hg⟩ := hin h
    have hh : τ h = action g := by rw [hα,←hg,autAction_inner]
    exact ⟨g,LinearMap.ext (fun v => congrArg Prod.fst (LinearMap.congr_fun hh (v,0))),
      LinearMap.ext (fun v => congrArg Prod.snd (LinearMap.congr_fun hh (0,v)))⟩
  let f : H →* (Vector ≃ₗ[ZMod 2] Vector) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp η.asGroupHom
  refine ⟨f,?_,rfl,?_⟩
  · intro g
    obtain ⟨k,hk⟩ := hq ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm g)
    refine ⟨k,?_⟩
    apply LinearEquiv.toLinearMap_injective
    change η k = g.toLinearMap
    rw [hn,hk]
    exact congrArg LinearEquiv.toLinearMap ((BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply g)
  · apply MonoidHom.ext
    intro h
    obtain ⟨g,hn',hd'⟩ := he h⁻¹
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change ν h v w = v (η h⁻¹ w)
    rw [hn']
    obtain ⟨g',hn'',hd''⟩ := he h
    rw [hd'']
    have hgg : W (g' * g) = W 1 := by
      rw [map_mul,←hn'',←hn',←map_mul,mul_inv_cancel,map_one,map_one]
    have hg : g = g'⁻¹ := eq_inv_of_mul_eq_one_right (natural_injective hgg)
    rw [hg]
    rfl
end BinaryLinearThree.NaturalDual
