module
public import Theory.Representation.IrreducibleMultiplicityBound

/-!
# Inequivalent simple constituents in a small repeated module

Two inequivalent simple modules cannot both embed in a space of dimension
less than the sum of their dimensions. Quotient by the first image; the
second image would then yield either an embedding in the smaller quotient
or an intertwiner between the simple modules. Applied coordinate by
coordinate, this excludes their direct sum from any repetition of that
small space, without semisimplicity of the target restriction.

Source application: Aschbacher--Smith 10.2.9, printed p.752, the original
natural--dual row inside repeated natural containing modules.
-/

public noncomputable section
namespace Representation.IntertwiningMap
variable {k H W Y X : Type*} [Field k] [Group H]
  [AddCommGroup W] [Module k W]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  {ρ : Representation k H W} {η : Representation k H Y}
  {σ : Representation k H X} [IsIrreducible ρ] [IsIrreducible η]

theorem small_inequivalent_pair
    (hzero : ∀ b : η.IntertwiningMap ρ, b = 0)
    (hd : Module.finrank k X < Module.finrank k W + Module.finrank k Y)
    (f : ρ.IntertwiningMap σ) (g : η.IntertwiningMap σ) :
    f = 0 ∨ g = 0 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  by_cases hg : g = 0
  · exact Or.inr hg
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let R := f.range
  let p : σ.IntertwiningMap R.quotientRepresentation := {
    toLinearMap := R.toSubmodule.mkQ
    isIntertwining' := by intros; rfl }
  have hq : p.comp g = 0 := by
    rcases IsIrreducible.injective_or_eq_zero (p.comp g) with hi | hz
    · have hlow := LinearMap.finrank_le_finrank_of_injective
        (f := (p.comp g).toLinearMap) hi
      have hr : Module.finrank k R.toSubmodule = Module.finrank k W :=
        (LinearEquiv.ofInjective f.toLinearMap hfi).finrank_eq.symm
      have hsum := Submodule.finrank_quotient_add_finrank R.toSubmodule
      omega
    · exact hz
  let e := LinearEquiv.ofInjective f.toLinearMap hfi
  have hgR (w : Y) : g w ∈ R.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun a : η.IntertwiningMap R.quotientRepresentation => a w) hq
  let b : Y →ₗ[k] W := e.symm.toLinearMap.comp
    (g.toLinearMap.codRestrict R.toSubmodule hgR)
  have hb (w : Y) : f (b w) = g w :=
    congrArg Subtype.val (e.apply_symm_apply ⟨g w,hgR w⟩)
  let b' : η.IntertwiningMap ρ := {
    toLinearMap := b
    isIntertwining' := by
      intro h
      ext w
      apply hfi
      change f (b (η h w)) = f (ρ h (b w))
      rw [hb,f.isIntertwining,g.isIntertwining,hb] }
  apply (hg ?_).elim
  ext w
  change g w = 0
  rw [←hb]
  change f (b' w) = 0
  rw [hzero b']
  exact f.map_zero
end Representation.IntertwiningMap

namespace Representation
variable {k H W Y X : Type*} [Field k] [Group H]
  [AddCommGroup W] [Module k W] [Nontrivial W]
  [AddCommGroup Y] [Module k Y] [Nontrivial Y]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  {ρ : Representation k H W} {η : Representation k H Y}
  [IsIrreducible ρ] [IsIrreducible η]

theorem no_small_repeated_inequivalent_pair
    (hzero : ∀ b : η.IntertwiningMap ρ, b = 0)
    (hd : Module.finrank k X < Module.finrank k W + Module.finrank k Y)
    {ι : Type*} (σ : Representation k H X)
    (τ : Representation k H (ι → X)) (hτ : ∀ h v i, τ h v i = σ h (v i))
    (f : (ρ.prod η).IntertwiningMap τ) (hfi : Function.Injective f) : False := by
  classical
  let a (i : ι) : ρ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.proj i).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro h
      ext w
      have he := congrFun (LinearMap.congr_fun (f.isIntertwining' h) (w,0)) i
      have he' := he.trans (hτ h _ i)
      change f (ρ h w,η h 0) i = σ h (f (w,0) i) at he'
      rw [map_zero] at he'
      exact he' }
  let b (i : ι) : η.IntertwiningMap σ := {
    toLinearMap := (LinearMap.proj i).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro h
      ext w
      have he := congrFun (LinearMap.congr_fun (f.isIntertwining' h) (0,w)) i
      have he' := he.trans (hτ h _ i)
      change f (ρ h 0,η h w) i = σ h (f (0,w) i) at he'
      rw [map_zero] at he'
      exact he' }
  have hex : ∃ i, a i ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    apply hw
    have he : f (w,0) = 0 := funext fun i =>
      congrArg (fun z : ρ.IntertwiningMap σ => z w) (hn i)
    exact congrArg Prod.fst (hfi (he.trans f.map_zero.symm))
  obtain ⟨i,hi⟩ := hex
  have hb (j : ι) : b j = 0 :=
    (IntertwiningMap.small_inequivalent_pair hzero hd (a i) (b j)).resolve_left hi
  obtain ⟨w,hw⟩ := exists_ne (0 : Y)
  apply hw
  have he : f (0,w) = 0 := funext fun j =>
    congrArg (fun z : η.IntertwiningMap σ => z w) (hb j)
  exact congrArg Prod.snd (hfi (he.trans f.map_zero.symm))
end Representation
