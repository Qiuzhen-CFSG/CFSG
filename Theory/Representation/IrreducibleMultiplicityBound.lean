module
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Multiplicity bounds from a simple orbit generator

When a simple module has only scalar endomorphisms and its dimension exceeds
half the target dimension, every map into the target is a scalar multiple of
one nonzero map. The quotient by that map's image is too small for another
simple image. Consequently a simple generator in repeated copies of a small
target generates at most one copy: any relation between coordinate maps is
preserved by the whole acting group.

The application is the repeated-natural containing row of Aschbacher--Smith
10.2.9, printed p.752. No semisimplicity of the restricted target is assumed.
-/

public noncomputable section
open Representation

namespace Representation.IntertwiningMap
variable {k H W X : Type*} [Field k] [Group H]
  [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  {ρ : Representation k H W} {σ : Representation k H X} [IsIrreducible ρ]
theorem small_target_scalar
    (hscalar : ∀ f : ρ.IntertwiningMap ρ, ∃ c : k, ∀ w, f w = c • w)
    (hd : Module.finrank k X < 2 * Module.finrank k W)
    (f g : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    ∃ c : k, ∀ w, g w = c • f w := by
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let R := f.range
  let p : σ.IntertwiningMap R.quotientRepresentation := {
    toLinearMap := R.toSubmodule.mkQ
    isIntertwining' := by intros; rfl }
  have hq : p.comp g = 0 := by
    rcases IsIrreducible.injective_or_eq_zero (p.comp g) with hi | hz
    · have hlow := LinearMap.finrank_le_finrank_of_injective (f := (p.comp g).toLinearMap) hi
      have hr : Module.finrank k R.toSubmodule = Module.finrank k W :=
        (LinearEquiv.ofInjective f.toLinearMap hfi).finrank_eq.symm
      have hsum := Submodule.finrank_quotient_add_finrank R.toSubmodule
      omega
    · exact hz
  let e := LinearEquiv.ofInjective f.toLinearMap hfi
  have hg (w : W) : g w ∈ R.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun a : ρ.IntertwiningMap R.quotientRepresentation => a w) hq
  let b : W →ₗ[k] W := e.symm.toLinearMap.comp (g.toLinearMap.codRestrict R.toSubmodule hg)
  have hb (w : W) : f (b w) = g w := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨g w,hg w⟩)
  let b' : ρ.IntertwiningMap ρ := {
    toLinearMap := b
    isIntertwining' := by
      intro h
      ext w
      apply hfi
      change f (b (ρ h w)) = f (ρ h (b w))
      rw [hb,f.isIntertwining,g.isIntertwining,hb] }
  obtain ⟨c,hc⟩ := hscalar b'
  refine ⟨c,fun w => ?_⟩
  rw [←hb]
  change f (b' w) = _
  rw [hc,map_smul]
end Representation.IntertwiningMap

namespace Representation
variable {k H A W X : Type*} [Field k] [Group H] [Group A]
  [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X] [Nontrivial X]
  {ρ : Representation k H W} [IsIrreducible ρ]
  (σ : Representation k A X) (q : H →* A)
  {r : ℕ} (τ : Representation k A (Fin r → X))
  (hτ : ∀ a v i, τ a v i = σ a (v i))
  (f : ρ.IntertwiningMap (τ.comp q))
  (hscalar : ∀ b : ρ.IntertwiningMap ρ, ∃ c : k, ∀ w, b w = c • w)
  (hd : Module.finrank k X < 2 * Module.finrank k W)
  (hgen : ∀ P : Subrepresentation τ, (∀ w, f w ∈ P.toSubmodule) → P = ⊤)

include σ q τ hτ f hscalar hd hgen in
/-- A simple generator of dimension greater than half a single summand
cannot generate two or more identically acted-on copies. -/
theorem copies_eq_one_of_small_simple_generator (hr : 0 < r) : r = 1 := by
  classical
  let g (i : Fin r) : ρ.IntertwiningMap (σ.comp q) := {
    toLinearMap := (LinearMap.proj i).comp f.toLinearMap
    isIntertwining' := by
      intro h
      ext w
      exact (congrFun (LinearMap.congr_fun (f.isIntertwining' h) w) i).trans (hτ (q h) (f w) i) }
  let i : Fin r := ⟨0,hr⟩
  have hgi : g i ≠ 0 := by
    intro hz
    let P : Subrepresentation τ := {
      toSubmodule := (LinearMap.proj i : (Fin r → X) →ₗ[k] X).ker
      apply_mem_toSubmodule := by
        intro a v hv
        change v i = 0 at hv
        change τ a v i = 0
        rw [hτ,hv,map_zero] }
    have hP : P = ⊤ := hgen P (fun w =>
      congrArg (fun b : ρ.IntertwiningMap (σ.comp q) => b w) hz)
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    have hm : (fun _ : Fin r => x) ∈ P.toSubmodule := hP ▸ Submodule.mem_top
    exact hx hm
  by_contra hn
  have hr2 : 1 < r := by omega
  let j : Fin r := ⟨1,hr2⟩
  obtain ⟨c,hc⟩ := IntertwiningMap.small_target_scalar hscalar hd (g i) (g j) hgi
  let P : Subrepresentation τ := {
    toSubmodule := ((LinearMap.proj j : (Fin r → X) →ₗ[k] X) - c • LinearMap.proj i).ker
    apply_mem_toSubmodule := by
      intro a v hv
      change v j - c • v i = 0 at hv
      change τ a v j - c • τ a v i = 0
      rw [hτ,hτ,←map_smul,←map_sub,hv,map_zero] }
  have hP : P = ⊤ := hgen P (fun w => sub_eq_zero.mpr (hc w))
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  have hm : (Pi.single j x) ∈ P.toSubmodule := hP ▸ Submodule.mem_top
  change (Pi.single j x : Fin r → X) j - c • (Pi.single j x : Fin r → X) i = 0 at hm
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
  apply hx
  simpa [hij,Ne.symm hij] using hm
end Representation
