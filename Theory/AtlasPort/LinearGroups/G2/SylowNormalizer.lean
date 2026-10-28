module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Intrinsic
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Normalizers
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry

/-!
# The normalizer of the positive-root Sylow subgroup of G₂

The central involutions and the second-central involutions of the positive
root group recover the highest-root and two-long-root subgroups. Their
normalizers are the two root parabolics, whose intersection is the stabilizer
of the standard flag, namely the Borel. Thus the Sylow normalizer is exactly
the Borel. Coefficient transport preserves this Sylow subgroup as well.

These intrinsic calculations support the Borel–field action in the proof of
Aschbacher–Smith Proposition 1.3.4, printed p.511. Root coordinates and flag
stabilizers come from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.SylowNormalizer
open Subgroup LieParabolicSetup SylowParabolicInvariance
open EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

variable {F K : Type*} [Field F] [Field K]

/-- The actual two standard parabolics intersect in the root-defined Borel. -/
theorem parabolics_intersection :
    parabolic₁ (F := F) ⊓ parabolic₂ = borel := by
  rw [shortParabolic_eq_lineStabilizer, parabolic₂, parabolic_eq_pointStabilizer,
    inf_comm]
  exact standardFlag_stabilizer

/-- Coefficient transport preserves the actual positive-root subgroup. -/
theorem field_map_unipotent (e : F ≃+* K) :
    (unipotent (K := F)).map (fieldEquiv e).toMonoidHom = unipotent := by
  ext g
  simp only [mem_map, unipotent_eq_range]
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨e ∘ t, (long_field_unipotentProduct e t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotentProduct (e.symm ∘ t), ⟨_, rfl⟩, ?_⟩
    change fieldEquiv e (unipotentProduct (e.symm ∘ t)) = _
    rw [long_field_unipotentProduct]
    congr 1
    funext i
    exact e.apply_symm_apply _

/-- The positive-root Sylow normalizer is the Borel, including over F₂. -/
theorem normalizer_unipotent [CharP F 2] :
    normalizer (unipotent (K := F) : Set (Model F)) = borel := by
  apply le_antisymm
  · intro g hg
    have hu := mem_normalizer_iff_map_conj_eq.mp hg
    have ha := map_eq_of_centralInvolutions unipotent highestRoot
      highestRoot_iff_centralInvolution (MulAut.conj g) hu
    have hb := map_eq_of_secondCentralInvolutions unipotent longRootLocal
      longRootLocal_iff_secondCentralInvolution (MulAut.conj g) hu
    have hga : g ∈ parabolic₁ := by
      rw [← normalizer_highestRoot]
      exact mem_normalizer_iff_map_conj_eq.mpr ha
    have hgb : g ∈ parabolic₂ := by
      rw [← normalizer_longRootLocal]
      exact mem_normalizer_iff_map_conj_eq.mpr hb
    rw [← parabolics_intersection]
    exact ⟨hga, hgb⟩
  · apply sup_le unipotent.le_normalizer
    exact le_normalizer_iff.mpr (fun _ ht _ hu => torus_normalizes_unipotent ht hu)

end Atlas.G2.SylowNormalizer
