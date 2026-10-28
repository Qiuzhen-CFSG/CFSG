module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupTheory.SylowNormalIntersection
import Mathlib.Tactic.Abel

/-!
# Stabilizers of Sylow-fixed vectors across a central quotient

On a quotient stabilizer, the displacement of a vector is a homomorphism
into the binary additive group when the kernel is fixed. If a Sylow two-group
fixes the vector, the homomorphism is trivial: its image has two-power order
and odd index. Thus the original and quotient vector stabilizers coincide.
For a normal subgroup with a Sylow supplement, centrality of the kernel is
needed only under the normal subgroup. No module extension is split.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
the orthogonal centralizer argument following 13.6.23, printed p.933.
-/

@[expose] public section
open Subgroup Representation
namespace Representation.SylowFixedCentralQuotient

private theorem binary_hom_eq_one {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (f : D →* Multiplicative V) (S : Sylow 2 D)
    (hS : (S : Subgroup D) ≤ f.ker) (d : D) : f d = 1 := by
  have htwo : IsPGroup 2 (Multiplicative V) := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    change x.toAdd + x.toAdd = 0
    have h := congrArg (fun c : ZMod 2 => c • x.toAdd) (show (2 : ZMod 2) = 0 by decide)
    simpa only [two_smul, zero_smul] using h
  have hfinite : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (htwo.to_subgroup f.range).exists_card_eq
  have hindex : f.ker.index = 2 ^ n := (index_ker f).trans hn
  have hn0 : n = 0 := by
    by_contra h
    exact S.not_dvd_index ((hindex ▸ dvd_pow_self 2 h).trans (index_dvd_of_le hS))
  have hk : f.ker = ⊤ := index_eq_one.mp (by simpa [hn0] using hindex)
  exact show d ∈ f.ker from hk ▸ mem_top d

private theorem fixed_of_central_displacement {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (S : Sylow 2 D) (v : V)
    (hS : ∀ s ∈ (S : Subgroup D), ρ s v = v)
    (hcentral : ∀ g h : D, ρ g (ρ h v - v) = ρ h v - v) :
    ∀ g, ρ g v = v := by
  let f : D →* Multiplicative V :=
    { toFun := fun g => Multiplicative.ofAdd (ρ g v - v)
      map_one' := by simp
      map_mul' := by
        intro g h
        change ρ (g * h) v - v = (ρ g v - v) + (ρ h v - v)
        have hh := hcentral g h
        rw [map_sub] at hh
        rw [map_mul, Module.End.mul_apply]
        calc
          _ = (ρ g (ρ h v) - ρ g v) + (ρ g v - v) := by abel
          _ = _ := by rw [hh]; abel }
  have hs : (S : Subgroup D) ≤ f.ker := by
    intro s hs
    change ρ s v - v = 0
    rw [hS s hs, sub_self]
  intro g
  exact sub_eq_zero.mp (binary_hom_eq_one f S hs g)

private def vectorStabilizer {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (v : V) : Subgroup D where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ a v = v at ha
    change ρ b v = v at hb
    change ρ (a * b) v = v
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha
    change ρ a v = v at ha
    change ρ a⁻¹ v = v
    have h := congrArg (ρ a⁻¹) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- Fixation of a Sylow-fixed vector is detected modulo a fixed kernel.
No splitting or surjectivity of the equivariant map is required. -/
theorem fixed_iff_of_central_kernel {D V W : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (q : V →ₗ[ZMod 2] W) (he : ∀ g v, q (ρ g v) = σ g (q v))
    (hc : ∀ g v, q v = 0 → ρ g v = v)
    (S : Sylow 2 D) (v : V) (hs : ∀ s ∈ (S : Subgroup D), ρ s v = v) :
    ∀ g, ρ g v = v ↔ σ g (q v) = q v := by
  let H := vectorStabilizer σ (q v)
  have hSH : (S : Subgroup D) ≤ H := by
    intro s hs'
    change σ s (q v) = q v
    rw [← he, hs s hs']
  have hfix : ∀ h : H, (ρ.comp H.subtype) h v = v := by
    apply fixed_of_central_displacement _ (S.subtype hSH) v
    · intro s hs'
      exact hs s hs'
    · intro g h
      apply hc
      change q (ρ (h : D) v - v) = 0
      rw [map_sub, he, h.property, sub_self]
  intro g
  constructor
  · intro hg
    rw [← he, hg]
  · intro hg
    exact hfix ⟨g, hg⟩

/-- With a normal subgroup and a Sylow supplement, it suffices for the kernel
to be fixed by the normal subgroup. The supplement already fixes the vector. -/
theorem fixed_iff_of_component_central_kernel {D V W : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (q : V →ₗ[ZMod 2] W) (he : ∀ g v, q (ρ g v) = σ g (q v))
    (K : Subgroup D) [K.Normal]
    (hc : ∀ k : K, ∀ v, q v = 0 → ρ k v = v)
    (S : Sylow 2 D) (hgen : K ⊔ (S : Subgroup D) = ⊤)
    (v : V) (hs : ∀ s ∈ (S : Subgroup D), ρ s v = v) :
    ∀ g, ρ g v = v ↔ σ g (q v) = q v := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal K
  have hfix := fixed_iff_of_central_kernel (ρ.comp K.subtype) (σ.comp K.subtype) q
    (fun k w => he k w) hc R v (by
      intro r hr
      have hr' : r ∈ (S : Subgroup D).subgroupOf K := hR ▸ hr
      exact hs r hr')
  intro g
  obtain ⟨k, hk, s, hs', rfl⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
  have hsq : σ s (q v) = q v := by rw [← he, hs s hs']
  have hh : ρ k v = v ↔ σ k (q v) = q v := hfix ⟨k, hk⟩
  simpa only [map_mul, Module.End.mul_apply, hs s hs', hsq] using hh

end Representation.SylowFixedCentralQuotient
