module
public import Theory.Representation.SchurCopies
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Extending a binary normal-subgroup action through its automorphisms

A normal subgroup acts in specified native coordinates. If its linear
centralizer is trivial, every ambient operator is the unique implementation
of its conjugation automorphism. Hence any native automorphism extension
agrees with the original action in those same coordinates. Absolute
irreducibility supplies the centralizer hypothesis over the binary field.

The consumers in Chapter G apply this to the actual M12 and M22 modules,
retaining outer involutions. Source: the scalar-centralizer argument in
Aschbacher--Smith G.11.7 and H.11.1, printed pp.367,392--393.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryNormalExtension
variable {D R U V : Type*} [Group D] [Group R]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup V] [Module (ZMod 2) V]

set_option backward.isDefEq.respectTransparency false in
theorem centralizer_eq_one_of_absolutelyIrreducible
    (σ : Representation (ZMod 2) R U) [FiniteDimensional (ZMod 2) U]
    [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    [Nontrivial U] (f : U ≃ₗ[ZMod 2] U)
    (hf : ∀ r u, f (σ r u) = σ r (f u)) : f = 1 := by
  let t : σ.IntertwiningMap σ := ⟨f.toLinearMap, by
    intro r
    ext u
    exact hf r u⟩
  obtain ⟨c,hc⟩ := (isAbsolutelyIrreducible_iff_surjective σ).mp inferInstance t
  have he (u : U) : f u = c • u := by
    exact (congrArg (fun q : σ.IntertwiningMap σ => q u) hc).symm
  have hc1 : c = 1 := by
    fin_cases c
    · obtain ⟨u,hu⟩ := exists_ne (0 : U)
      exact (hu (f.injective (by simpa using he u))).elim
    · rfl
  ext u
  change f u = u
  simpa only [hc1,one_smul] using he u

private theorem intertwiner_unique
    (σ : Representation (ZMod 2) R U)
    (hc : ∀ f : U ≃ₗ[ZMod 2] U,
      (∀ r u, f (σ r u) = σ r (f u)) → f = 1)
    (a : MulAut R) (f g : U ≃ₗ[ZMod 2] U)
    (hf : ∀ r u, f (σ r u) = σ (a r) (f u))
    (hg : ∀ r u, g (σ r u) = σ (a r) (g u)) : f = g := by
  have he : f.trans g.symm = 1 := hc _ (by
    intro r u
    apply g.injective
    change g (g.symm (f (σ r u))) = g (σ r (g.symm (f u)))
    rw [g.apply_symm_apply,hf,hg,g.apply_symm_apply])
  ext u
  have hu := LinearEquiv.congr_fun he u
  change g.symm (f u) = u at hu
  exact g.symm.injective (hu.trans (g.symm_apply_apply u).symm)

/-- A native extension agrees with the original ambient action when the
normal subgroup has trivial linear centralizer. -/
theorem equivariant (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (σ : Representation (ZMod 2) R U) (τ : Representation (ZMod 2) (MulAut R) U)
    (hi : τ.comp MulAut.conj = σ)
    (hc : ∀ f : U ≃ₗ[ZMod 2] U,
      (∀ r u, f (σ r u) = σ r (f u)) → f = 1)
    (e : L ≃* R) (f : V ≃ₗ[ZMod 2] U)
    (hf : ∀ l : L, ∀ v, f (ρ l v) = σ (e l) (f v))
    (g : D) (v : V) :
    f (ρ g v) = τ (MulAut.congr e (MulAut.conjNormal g)) (f v) := by
  let q : Representation (ZMod 2) D U := f.conjRingEquiv.toMonoidHom.comp ρ
  let a := MulAut.congr e (MulAut.conjNormal (H := L) g)
  have hq (l : L) : q l = σ (e l) := by
    ext u
    change f (ρ l (f.symm u)) = σ (e l) u
    rw [hf,f.apply_symm_apply]
  have hleft (r : R) (u : U) : q g (σ r u) = σ (a r) (q g u) := by
    let l := e.symm r
    let s := MulAut.conjNormal (H := L) g l
    have hl : e l = r := e.apply_symm_apply r
    have hs : e s = a r := rfl
    have hmul : g * (l : D) = (s : D) * g := by
      change g * (l : D) = (g * (l : D) * g⁻¹) * g
      group
    have hh : q g * σ r = σ (a r) * q g := by
      rw [←hl,←hq,←map_mul,hmul,map_mul,hq,hs,hl]
    exact congrArg (fun m : Module.End (ZMod 2) U => m u) hh
  have hin (r : R) : τ (MulAut.conj r) = σ r :=
    congrArg (fun p : Representation (ZMod 2) R U => p r) hi
  have hright (r : R) (u : U) : τ a (σ r u) = σ (a r) (τ a u) := by
    have hm : a * MulAut.conj r = MulAut.conj (a r) * a := by
      ext x
      simp [MulAut.conj_apply]
    have hh : τ a * σ r = σ (a r) * τ a := by
      rw [←hin,←hin,←map_mul,←map_mul,hm]
    exact congrArg (fun m : Module.End (ZMod 2) U => m u) hh
  have he := intertwiner_unique σ hc a
    (LinearMap.GeneralLinearGroup.toLinearEquiv (q.asGroupHom g))
    (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom a)) hleft hright
  have hv := LinearEquiv.congr_fun he (f v)
  change f (ρ g (f.symm (f v))) = τ a (f v) at hv
  simpa only [f.symm_apply_apply] using hv
end Representation.BinaryNormalExtension
