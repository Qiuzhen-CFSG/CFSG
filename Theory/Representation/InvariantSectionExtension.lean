module
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RepresentationTheory.Invariants

/-!
# Extending coordinates over an invariant supplement

If V = U + C and an equivariant surjection on U has kernel U ∩ C, it
extends uniquely by zero on C to an equivariant surjection on V with kernel
C. The map descends through the kernel of U × C → V, so the construction
needs no direct sum or invariant complement. The fixed space of a normal
subgroup is invariant under the full actor and can serve as C.

The application following Aschbacher–Smith 13.6.23 (printed p.933,
PDF p.950) first proves the required sum by odd-coset averaging, then
extends the moved-section coordinates to the original seed span.
-/

@[expose] public section
namespace Representation
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The fixed space of a normal subgroup is invariant under the entire actor. -/
noncomputable def normalFixedSubrepresentation (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] : Subrepresentation ρ where
  toSubmodule := Representation.invariants (ρ.comp N.subtype)
  apply_mem_toSubmodule g v hv n := by
    have hn := hv ⟨g⁻¹ * n * g, by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n n.property g⁻¹⟩
    change ρ n (ρ g v) = ρ g v
    calc
      _ = ρ g (ρ (g⁻¹ * n * g) v) := by
        simp only [map_mul, Module.End.mul_apply]
        simp
      _ = ρ g v := congrArg (ρ g) hn

/-- Extend a section map by zero on an invariant supplement. -/
theorem exists_extension_by_zero
    (ρ : Representation k G V) (σ : Representation k G W)
    (U C : Subrepresentation ρ) (hUC : U.toSubmodule ⊔ C.toSubmodule = ⊤)
    (f : U.toSubmodule →ₗ[k] W) (hf : Function.Surjective f)
    (he : ∀ g u, f (U.toRepresentation g u) = σ g (f u))
    (hk : ∀ u, f u = 0 ↔ u.val ∈ C.toSubmodule) :
    ∃ p : V →ₗ[k] W, Function.Surjective p ∧
      (∀ g v, p (ρ g v) = σ g (p v)) ∧
      (∀ v, p v = 0 ↔ v ∈ C.toSubmodule) ∧ (∀ u, p u.val = f u) := by
  let q : U.toSubmodule × C.toSubmodule →ₗ[k] V :=
    U.toSubmodule.subtype.coprod C.toSubmodule.subtype
  let F : U.toSubmodule × C.toSubmodule →ₗ[k] W := f.comp (LinearMap.fst k _ _)
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp (hUC ▸ Submodule.mem_top (x := v))
    exact ⟨(⟨u, hu⟩, ⟨c, hc⟩), huc⟩
  have hker : q.ker ≤ F.ker := by
    rintro ⟨u, c⟩ h
    change (u : V) + c = 0 at h
    change f u = 0
    exact (hk u).mpr (by rw [eq_neg_of_add_eq_zero_left h]; exact C.toSubmodule.neg_mem c.property)
  let p := (q.ker.liftQ F hker).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hp (u : U.toSubmodule) (c : C.toSubmodule) : p ((u : V) + c) = f u := by
    change q.ker.liftQ F hker ((q.quotKerEquivOfSurjective hq).symm (q (u, c))) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hu (u : U.toSubmodule) : p u.val = f u := by
    simpa only [Submodule.coe_zero, add_zero] using hp u 0
  refine ⟨p, ?_, ?_, ?_, hu⟩
  · intro w
    obtain ⟨u, rfl⟩ := hf w
    exact ⟨u.val, hu u⟩
  · intro g v
    obtain ⟨⟨u, c⟩, rfl⟩ := hq v
    change p (ρ g ((u : V) + c)) = σ g (p ((u : V) + c))
    rw [map_add, hp]
    exact (hp (U.toRepresentation g u) (C.toRepresentation g c)).trans (he g u)
  · intro v
    obtain ⟨⟨u, c⟩, rfl⟩ := hq v
    change p ((u : V) + c) = 0 ↔ (u : V) + c ∈ C.toSubmodule
    rw [hp, hk, C.toSubmodule.add_mem_iff_left c.property]
/-- The extension is determined by its values on the two summands; no
complement or choice of decomposition affects it. -/
theorem extension_by_zero_unique
    (U C : Submodule k V) (hUC : U ⊔ C = ⊤)
    (p q : V →ₗ[k] W)
    (hU : ∀ u : U, p u.val = q u.val)
    (hp : ∀ c ∈ C, p c = 0) (hq : ∀ c ∈ C, q c = 0) : p = q := by
  ext v
  obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (hUC ▸ Submodule.mem_top (x := v))
  rw [map_add, map_add, hp c hc, hq c hc, hU ⟨u, hu⟩]

end Representation
