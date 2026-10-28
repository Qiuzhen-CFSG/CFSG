module

public import Theory.Representation.SymplecticFourOrthogonalCover.Roots

/-!
# Conjugate transvection geometry over the original projections

Conjugation g r g⁻¹ transports displacement images by the actual operator g.
The natural projection intertwines these operators, so the conjugated line's
preimage is the image of the original preimage. This proves the commutator,
fixedness, dimension, nonsingularity and disjointness assertions for every
L-conjugate root. The compatible universal-cover quotient transports the
commutator and centrality identities to arbitrary binary covers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1b),(3),
printed p.413/PDF p.424. No Sylow identification is assumed here.
-/

@[expose] public section
noncomputable section

namespace Representation.SymplecticFourOrthogonalCover.Roots
open Representation.OneCohomology
open ClassicalOrthogonal

section Transport
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

private lemma conj_displacement (ρ : Representation k G V) (g r : G) (v : V) :
    ρ (g * r * g⁻¹) v - v = ρ g (ρ r (ρ g⁻¹ v) - ρ g⁻¹ v) := by
  simp only [map_sub, map_mul, Module.End.mul_apply, self_inv_apply]

private lemma conjugate_coinvariants (ρ : Representation k G V) (R : Subgroup G) (g : G) :
    Coinvariants.ker (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype) =
      (Coinvariants.ker (ρ.comp R.subtype)).map (ρ g) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨r, v⟩, rfl⟩
    obtain ⟨s, hs, he⟩ := r.property
    change ρ r.val v - v ∈ _
    change g * s * g⁻¹ = r.val at he
    rw [← he, conj_displacement]
    exact ⟨ρ s (ρ g⁻¹ v) - ρ g⁻¹ v,
      Coinvariants.sub_mem_ker (ρ := ρ.comp R.subtype) ⟨s, hs⟩ _, rfl⟩
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨r, v⟩, rfl⟩
    change ρ g (ρ r.val v - v) ∈ Coinvariants.ker (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype)
    have he := conj_displacement ρ g r.val (ρ g v)
    rw [inv_self_apply] at he
    rw [← he]
    exact Coinvariants.sub_mem_ker
      (ρ := ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨g * r.val * g⁻¹, Subgroup.mem_map.mpr ⟨r.val, r.property, rfl⟩⟩ _

private lemma conjugate_fixed (ρ : Representation k G V) (R : Subgroup G) (g : G)
    (A : Submodule k V) (hA : A ≤ fixed (ρ.comp R.subtype)) :
    A.map (ρ g) ≤ fixed (ρ.comp (R.map (MulAut.conj g).toMonoidHom).subtype) := by
  rintro _ ⟨v, hv, rfl⟩ r
  obtain ⟨s, hs, he⟩ := r.property
  change ρ r.val (ρ g v) = ρ g v
  change g * s * g⁻¹ = r.val at he
  rw [← he, map_mul, map_mul]
  change ρ g (ρ s (ρ g⁻¹ (ρ g v))) = _
  rw [inv_self_apply]
  exact congrArg (ρ g) (hA hv ⟨s, hs⟩)
end Transport

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

def conjugateGroup (g : L (K := K)) : Subgroup (L (K := K)) :=
  group.map (MulAut.conj g).toMonoidHom

def conjugateLine (g : L (K := K)) : Submodule K (Natural (K := K)) :=
  firstLine.map (symplecticDerivedNatural 2 g)

lemma conjugate_preimage (g : L (K := K)) :
    (conjugateLine g).comap projection.toLinearMap = firstPreimage.map (action g) := by
  ext v
  constructor
  · rintro ⟨w, hw, he⟩
    change symplecticDerivedNatural 2 g w = projection v at he
    refine ⟨action g⁻¹ v, ?_, self_inv_apply action g v⟩
    change projection (action g⁻¹ v) ∈ firstLine
    rw [(projection (K := K)).isIntertwining, ← he, inv_self_apply]
    exact hw
  · rintro ⟨w, hw, rfl⟩
    exact ⟨projection w, hw, (LinearMap.congr_fun ((projection (K := K)).isIntertwining' g) w).symm⟩

lemma conjugate_root_geometry (hcard : 2 < Nat.card K) (g : L (K := K)) :
    (conjugateLine g).comap projection.toLinearMap =
        Coinvariants.ker (action.comp (conjugateGroup g).subtype) ∧
      (conjugateLine g).comap projection.toLinearMap ≤
        fixed (action.comp (conjugateGroup g).subtype) := by
  rw [conjugate_preimage]
  constructor
  · rw [conjugateGroup, conjugate_coinvariants, root_commutator hcard]
  · exact conjugate_fixed action group g firstPreimage (firstPreimage_fixed hcard)

lemma conjugate_displacement (hcard : 2 < Nat.card K) (g : L (K := K)) (t : K) :
    LinearMap.range (action (g * element hcard t * g⁻¹) - LinearMap.id) =
      (rootDisplacement hcard t).map (action g) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨action (element hcard t) (action g⁻¹ w) - action g⁻¹ w, ⟨action g⁻¹ w, rfl⟩, ?_⟩
    exact (conj_displacement action g (element hcard t) w).symm
  · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
    refine ⟨action g u, ?_⟩
    change action (g * element hcard t * g⁻¹) (action g u) - action g u = _
    rw [conj_displacement, inv_self_apply]
    rfl

lemma conjugate_displacement_geometry (hcard : 2 < Nat.card K)
    (g : L (K := K)) (t : K) (ht : t ≠ 0) :
    let D := LinearMap.range (action (g * element hcard t * g⁻¹) - LinearMap.id)
    Module.finrank K D = 1 ∧ D ≤ (conjugateLine g).comap projection.toLinearMap ∧
      (∀ v ∈ D, v ≠ 0 → formB 2 K v ≠ 0) ∧ D ≠ radical := by
  dsimp only
  rw [conjugate_displacement, conjugate_preimage]
  have hi := (action (K := K)).apply_bijective g |>.1
  refine ⟨?_, Submodule.map_mono (rootDisplacement_le_firstPreimage hcard t), ?_, ?_⟩
  · rw [← (Submodule.equivMapOfInjective (action g) hi _).finrank_eq]
    exact rootDisplacement_dimension hcard t ht
  · rintro _ ⟨v, hv, rfl⟩ hn
    rw [action_preserves]
    exact rootDisplacement_nonsingular hcard t ht v hv (fun he => hn (by rw [he, map_zero]))
  · intro he
    have hm : vector t ∈ rootDisplacement hcard t := by
      rw [rootDisplacement_eq_span]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hv : action g (vector t) ∈ radical := he ▸ Submodule.mem_map_of_mem hm
    have hf := radical_fixed hv g⁻¹
    rw [inv_self_apply] at hf
    have hv' : vector t ∈ radical := hf.symm ▸ hv
    have hh := congrFun ((mem_radical _).mp hv') (.inl 0)
    exact ht (by simpa [vector, e] using hh)

lemma conjugate_displacements_disjoint (hcard : 2 < Nat.card K)
    (g : L (K := K)) (s t : K) (hs : s ≠ 0) (hst : s ≠ t) :
    Disjoint (LinearMap.range (action (g * element hcard s * g⁻¹) - LinearMap.id))
      (LinearMap.range (action (g * element hcard t * g⁻¹) - LinearMap.id)) := by
  rw [conjugate_displacement, conjugate_displacement]
  apply Submodule.disjoint_map_of_ker_le_right (rootDisplacement_disjoint hcard s t hs hst)
  rw [LinearMap.ker_eq_bot.mpr ((action (K := K)).apply_bijective g).1]
  exact bot_le

section Binary
variable [Algebra (ZMod 2) K]

lemma cover_conjugate_root_geometry (hcard : 2 < Nat.card K) (g : L (K := K))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    fixed σ ≤ ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap ∧
      ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap =
        Coinvariants.ker (σ.comp (conjugateGroup g).subtype) ∧
      ((conjugateLine g).restrictScalars (ZMod 2)).comap p.toLinearMap ≤
        fixed (σ.comp (conjugateGroup g).subtype) := by
  obtain ⟨f, hf, hover⟩ := exists_cover_quotient p hp
  have hg := conjugate_root_geometry hcard g
  refine ⟨fixed_le_preimage p _ (by rw [binary_natural_fixed]; exact bot_le), ?_⟩
  apply preimage_root_geometry_of_surjective binaryProjection p f hf hover (conjugateGroup g)
  · change (((conjugateLine g).comap projection.toLinearMap).restrictScalars (ZMod 2)) =
      Coinvariants.ker (restrictScalars (k := ZMod 2) (action.comp (conjugateGroup g).subtype))
    rw [coinvariants_restrictScalars, hg.1]
  · exact hg.2
end Binary
end Representation.SymplecticFourOrthogonalCover.Roots
