module

public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Binary

/-!
# The Sylow normalizer in the actual binary derived G₂ group

Let D = G₂(2)′ and R = U ∩ D. The central involutions of R recover the
highest-root group, and the involutions in its second center recover the
two-long-root group. Every element normalizing R therefore normalizes both
root groups. Their normalizers are the two standard parabolics, whose
intersection is the Borel U over the binary field. Conversely U normalizes
R, since D is normal. Thus N_G₂(2)(R) = U, and N_D(R) = R.

This treats the proper derived carrier appearing in Aschbacher–Smith,
B.5.5(1)(iv) and B.5.6, printed pp.104–105, and the Borel argument in
15.3.49(k), printed p.1144. The binary intersection, intrinsic root
characterizations and parabolic geometry come from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.DerivedNormalizerSolvable
open Subgroup LieParabolicSetup SylowParabolicInvariance BinaryParabolicPair

/-- The ambient normalizer of the actual derived binary Sylow group. -/
theorem binary_normalizer_derivedSylowAmbient :
    normalizer (derivedSylowAmbient : Set (Model (ZMod 2))) = unipotent := by
  apply le_antisymm
  · intro g hg
    have hu := mem_normalizer_iff_map_conj_eq.mp hg
    have ha := map_eq_of_centralInvolutions derivedSylowAmbient highestRoot
      binary_highestRoot_iff (MulAut.conj g) hu
    have hb := map_eq_of_secondCentralInvolutions derivedSylowAmbient longRootLocal
      binary_longRootLocal_iff (MulAut.conj g) hu
    have hga : g ∈ parabolic₁ := by
      rw [← normalizer_highestRoot]
      exact mem_normalizer_iff_map_conj_eq.mpr ha
    have hgb : g ∈ parabolic₂ := by
      rw [← normalizer_longRootLocal]
      exact mem_normalizer_iff_map_conj_eq.mpr hb
    have hB : g ∈ borel := by
      rw [← SylowNormalizer.parabolics_intersection]
      exact ⟨hga,hgb⟩
    rwa [borel_eq_unipotent_of_card_two (by simp)] at hB
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    exact ⟨(mem_normalizer_iff.mp (unipotent.le_normalizer hg) x).mp hx.1,
      (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem x hx.2 g⟩

/-- Restricting the ambient equality gives the normalizer inside the commutator group. -/
theorem binary_normalizer_restricted_unipotent :
    normalizer (unipotent.subgroupOf DerivedModel : Set DerivedModel) =
      unipotent.subgroupOf DerivedModel := by
  have hR : derivedSylowAmbient.subgroupOf DerivedModel =
      unipotent.subgroupOf DerivedModel := by
    ext x
    exact and_iff_left x.property
  rw [← hR, ← subgroupOf_normalizer_eq (show derivedSylowAmbient ≤ DerivedModel from inf_le_right),
    binary_normalizer_derivedSylowAmbient, hR]

/-- The actual binary derived Sylow subgroup is self-normalizing. -/
theorem binary_normalizer_derivedSylow :
    normalizer (derivedSylow : Set DerivedModel) = (derivedSylow : Subgroup DerivedModel) := by
  have hP : (derivedSylow : Subgroup DerivedModel) = unipotent.subgroupOf DerivedModel := by
    apply map_injective (f := DerivedModel.subtype) DerivedModel.subtype_injective
    rw [derivedSylow_map_subtype, subgroupOf_map_subtype]
    rfl
  change normalizer ((derivedSylow : Subgroup DerivedModel) : Set DerivedModel) = _
  rw [hP, binary_normalizer_restricted_unipotent]

end Atlas.G2.DerivedNormalizerSolvable
