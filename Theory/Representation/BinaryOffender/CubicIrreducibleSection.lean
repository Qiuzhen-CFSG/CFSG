module

public import Theory.Representation.BinaryOffender.CentralSectionSplitting

/-!
# Faithful irreducible central sections with a central cubic element

A nonidentity central element of order three has no fixed vector in a faithful
irreducible binary representation. Its norm operator therefore vanishes.
If an intertwining map onto such a representation has fixed kernel, the norm
on its domain has fixed image. Full commutator generation forces that norm to
vanish as well, so the fixed kernel is zero. No splitting is assumed.

This is the central-kernel recovery argument for the triple-cover case of
Aschbacher–Smith, B.5.1 and the final proof of 15.3.1, printed pp.99 and 1155
(combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The cubic norm vanishes on a faithful irreducible binary module when its
central cubic element acts nontrivially. -/
theorem centralCubicNorm_eq_zero_of_irreducible (ρ : Representation (ZMod 2) G V) (hirr : IsIrreducible ρ)
    (hf : Function.Injective ρ) (z : G) (hz : z ∈ center G)
    (hne : z ≠ 1) (hz3 : z ^ 3 = 1) : centralCubicNorm ρ z = 0 := by
  have hcomm (g : G) (v : V) : ρ z (ρ g v) = ρ g (ρ z v) := by
    change (ρ z * ρ g) v = (ρ g * ρ z) v
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hz g).symm]
  let K : Subrepresentation ρ :=
    ⟨(ρ z - 1).ker, by
      intro g v hv
      change ρ z v - v = 0 at hv
      change ρ z (ρ g v) - ρ g v = 0
      rw [hcomm, sub_eq_zero.mp hv, sub_self]⟩
  have hK : K = ⊥ := by
    rcases hirr.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      apply hne
      apply hf
      rw [map_one]
      ext v
      have hv : v ∈ K := by rw [h]; trivial
      exact sub_eq_zero.mp hv
  have hcubic (v : V) : ρ z (ρ z (ρ z v)) = v := by
    calc
      _ = ρ (z ^ 3) v := by simp [pow_succ, map_mul, Module.End.mul_apply]
      _ = v := by rw [hz3, map_one]; rfl
  apply LinearMap.ext
  intro v
  have hv : centralCubicNorm ρ z v ∈ K := by
    change ρ z (centralCubicNorm ρ z v) - centralCubicNorm ρ z v = 0
    rw [centralCubicNorm_apply, map_add, map_add, hcubic]
    abel
  rw [hK] at hv
  exact hv

/-- A fully moved module has no fixed kernel above a faithful irreducible
section with a nonidentity central cubic element. -/
theorem injective_of_central_cubic_irreducible_target (ρ : Representation (ZMod 2) G V)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hker : f.ker ≤ fixedSpace ρ ⊤)
    (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hi : IsIrreducible σ) (hf : Function.Injective σ)
    (z : G) (hz : z ∈ center G) (hne : z ≠ 1) (hz3 : z ^ 3 = 1) :
    Function.Injective f := by
  have hn := centralCubicNorm_eq_zero_of_irreducible σ hi hf z hz hne hz3
  have hnorm (v : V) : centralCubicNorm ρ z v ∈ fixedSpace ρ ⊤ := by
    apply hker
    change f (centralCubicNorm ρ z v) = 0
    have h := LinearMap.congr_fun hn (f v)
    simpa only [centralCubicNorm_apply, map_add, he, LinearMap.zero_apply] using h
  have hzero := centralCubicNorm_eq_zero_on_commutator ρ ⊤ ⊤ hm z
    (fun g _ => (mem_center_iff.mp hz g).symm) (fun v _ => hnorm v)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hfix : ρ z v = v := hker hv ⟨z, mem_top z⟩
  have h := hzero v Submodule.mem_top
  rw [centralCubicNorm_apply, hfix, hfix] at h
  have htwo : v + v = 0 := by
    have h := @two_smul (ZMod 2) V _ _ _ v
    simpa only [show (2 : ZMod 2) = 0 by decide, zero_smul] using h.symm
  simpa only [htwo, zero_add] using h

end Representation.BinaryOffender
