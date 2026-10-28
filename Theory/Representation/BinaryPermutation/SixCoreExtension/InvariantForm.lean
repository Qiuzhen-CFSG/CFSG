module
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Offender
public import Theory.Representation.BinaryPermutationSixCover.Facts
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The constant line obstructs invariant nondegenerate forms

The six-letter augmentation core is commutator-generated, while its
constant line is fixed. In a core-plus-fixed extension every invariant
bilinear form therefore annihilates that line. An injective core embedding
rules out a nondegenerate invariant form on the whole extension.

Source: Aschbacher--Smith B.3.1–3, augmentation-core structure; used in
the binary hexad comparison of I.2.2(6) and 2.3.9(7).
-/

public section
namespace BinaryPermutation.SixCoreExtension
open Representation

private theorem invariant_functional_zero (f : V →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ g v, f (coreAltRepresentation g v) = f v) : f = 0 := by
  have hk : Coinvariants.ker coreAltRepresentation ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change f (coreAltRepresentation g v - v) = 0
    rw [map_sub,hf,sub_self]
  have ht : Coinvariants.ker coreAltRepresentation = ⊤ := alternatingSix_core_generated
  rw [ht] at hk
  apply LinearMap.ext
  intro v
  exact hk Submodule.mem_top

private theorem constant_fixed (g : A) : coreAltRepresentation g constant = constant := by
  apply Subtype.ext
  change representation (Fin 6) g.val constant.val = constant.val
  have hc : constant.val = allOne (Fin 6) := by decide
  rw [hc,permute_allOne]

/-- The actual constant vector is in the left radical of every invariant form. -/
theorem constant_radical_of_fixed_supplement {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    (j : V →ₗ[ZMod 2] W)
    (he : ∀ a v, j (coreAltRepresentation a v) = ρ a (j v))
    (hgen : j.range ⊔ ρ.invariants = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W)
    (hB : ∀ a v w, B (ρ a v) (ρ a w) = B v w) :
    ∀ w, B (j constant) w = 0 := by
  have hk (a : A) : ρ a (j constant) = j constant := by rw [← he,constant_fixed]
  have hleft (v : V) : B (j constant) (j v) = 0 := by
    have hf := invariant_functional_zero ((B (j constant)).comp j) (by
      intro a v
      change B (j constant) (j (coreAltRepresentation a v)) = B (j constant) (j v)
      rw [he]
      simpa only [hk] using hB a (j constant) (j v))
    exact LinearMap.congr_fun hf v
  have hright (c : W) (hc : c ∈ ρ.invariants) : B (j constant) c = 0 := by
    have hf := invariant_functional_zero ((B.flip c).comp j) (by
      intro a v
      change B (j (coreAltRepresentation a v)) c = B (j v) c
      rw [he]
      simpa only [hc a] using hB a (j v) c)
    exact LinearMap.congr_fun hf constant
  intro w
  have hw : w ∈ j.range ⊔ ρ.invariants := hgen ▸ Submodule.mem_top
  obtain ⟨v,⟨u,rfl⟩,c,hc,rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add,hleft,hright c hc,add_zero]

/-- A faithful copy of the core with a fixed supplement admits no invariant
nondegenerate bilinear form. -/
theorem not_nondegenerate_of_fixed_supplement {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W)
    (j : V →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ a v, j (coreAltRepresentation a v) = ρ a (j v))
    (hgen : j.range ⊔ ρ.invariants = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W)
    (hB : ∀ a v w, B (ρ a v) (ρ a w) = B v w) : ¬ B.Nondegenerate := by
  intro hnd
  have hh : j constant ∈ B.ker := by
    apply LinearMap.ext
    exact constant_radical_of_fixed_supplement ρ j he hgen B hB
  rw [hnd.ker_eq_bot] at hh
  have hk : constant = 0 := hj ((show j constant = 0 from hh).trans j.map_zero.symm)
  have hne : constant ≠ 0 := by decide
  exact hne hk

end BinaryPermutation.SixCoreExtension
