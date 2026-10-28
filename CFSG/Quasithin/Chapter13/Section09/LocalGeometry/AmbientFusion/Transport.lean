module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion.SquareAction
public import Stellmacher.ElementaryAbelianMaxFusion

/-!
# Transport of local normalizers through the marked inclusion

The actual embedding carries the native two-core to the ambient two-core of M.
Normalizer preimages and the maximum-elementary family then transport the
native wreath calculations to the original Sylow and local subgroup.

Source: Aschbacher–Smith 13.9.2(2–4), printed p.969.
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)
include m

theorem image_twoCore : m.image (pCore 2 W) = d.M.pCoreIn 2 := by
  change (pCore 2 W).map (d.M.subtype.comp m.equiv.symm.toMonoidHom) = _
  rw [← map_map, pCore_map_iso]
  rfl

theorem embedding_mem_normalizer_image (H : Subgroup W) (w : W) :
    m.embedding w ∈ normalizer (m.image H : Set G) ↔ w ∈ normalizer (H : Set W) := by
  change w ∈ (normalizer (H.map m.embedding)).comap m.embedding ↔ _
  rw [comap_normalizer_eq_of_le_range (map_le_range m.embedding H),
    comap_map_eq_self_of_injective m.embedding_injective]

theorem image_le_normalizer_image {H K : Subgroup W}
    (h : H ≤ normalizer (K : Set W)) : m.image H ≤ normalizer (m.image K : Set G) :=
  (map_mono h).trans (K.le_normalizer_map m.embedding)

theorem normalizer_elementary_of_native_core
    (hA : SymmetricFourWreath.A = pCore 2 W) :
    normalizer (m.elementaryGroup true true : Set G) = d.M := by
  have h : m.elementaryGroup true true = d.M.pCoreIn 2 := by
    change m.image SymmetricFourWreath.A = _
    rw [hA, m.image_twoCore]
  rw [h, d.normalizer_twoCore]

theorem thompson_normalizer_of_native
    (hA : SymmetricFourWreath.A = pCore 2 W)
    (hJ : normalizer (SymmetricFourWreath.J : Set W) = (standardSylow : Subgroup W)) :
    normalizer (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) : Set G) =
      (d.T : Subgroup G) := by
  apply normalizer_eq_sylow_of_elementary_stabilizer m
  intro g hg hga
  have hgM : g ∈ d.M := m.normalizer_elementary_of_native_core hA ▸ hga
  obtain ⟨w, rfl⟩ := show g ∈ m.embedding.range by rwa [m.range_embedding]
  have hw : w ∈ normalizer (SymmetricFourWreath.J : Set W) := by
    apply (m.embedding_mem_normalizer_image SymmetricFourWreath.J w).mp
    change m.embedding w ∈ normalizer (Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) : Set G) at hg
    rwa [m.elementary_thompson] at hg
  rw [hJ] at hw
  rw [← m.image_standardSylow]
  exact mem_map_of_mem m.embedding hw

theorem maximum_elementary_normalized_of_native
    (hn : ∀ b c, SymmetricFourWreath.J ≤ normalizer (SymmetricFourWreath.elementary b c : Set W))
    (E : Subgroup G) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups (d.T : Subgroup G)) :
    Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) ≤ normalizer (E : Set G) := by
  obtain ⟨b,c,rfl⟩ := (maximum_elementary m E).mp hE
  rw [m.elementary_thompson]
  exact m.image_le_normalizer_image (hn b c)

end CFSG.Quasithin.Chapter13.Section09.Marking
