module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Marking
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry

/-!
# The original Sylow's four maximum elementary subgroups

Transport the proved wreath elementary family through the marking aligned
with the original Sylow subgroup. This identifies its elementary Thompson
subgroup with the actual dihedral base and with the join of the two diagonal
four-group products. No abstract replacement for the ambient Sylow is used.

Source: Aschbacher–Smith 13.9.2(1), printed p.969 (PDF p.986).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem maximum_elementary (E : Subgroup G) :
    E ∈ Stellmacher.elementaryAbelianMaxSubgroups (d.T : Subgroup G) ↔
      ∃b c, E = m.elementaryGroup b c := by
  constructor
  · intro hE
    let D := E.comap m.embedding
    have hbase : E ≤ m.embedding.range := by
      rw [m.range_embedding]
      exact hE.1.trans d.sylow_le
    have he : D.map m.embedding=E := map_comap_eq_self hbase
    have hD : D ∈ Stellmacher.elementaryAbelianMaxSubgroups (standardSylow : Subgroup W) := by
      apply (Stellmacher.maxFamily_map_injective_iff m.embedding m.embedding_injective
        (standardSylow : Subgroup W) D).mp
      change D.map m.embedding ∈ Stellmacher.elementaryAbelianMaxSubgroups (m.image _)
      rw [he,m.image_standardSylow]
      exact hE
    obtain ⟨b,c,hbc⟩ := (SymmetricFourWreath.maximum_elementary D).mp hD
    exact ⟨b,c,he.symm.trans (congrArg (fun S : Subgroup W=>S.map m.embedding) hbc)⟩
  · rintro ⟨b,c,rfl⟩
    have h := (Stellmacher.maxFamily_map_injective_iff m.embedding m.embedding_injective
      (standardSylow : Subgroup W) (SymmetricFourWreath.elementary b c)).mpr
      ((SymmetricFourWreath.maximum_elementary _).mpr ⟨b,c,rfl⟩)
    change m.elementaryGroup b c ∈ Stellmacher.elementaryAbelianMaxSubgroups (m.image _) at h
    rwa [m.image_standardSylow] at h

theorem elementary_thompson : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) = m.dihedralBase := by
  rw [←m.image_standardSylow]
  change Stellmacher.elementaryAbelianMaxJ ((standardSylow : Subgroup W).map m.embedding) = _
  rw [Stellmacher.elementaryAbelianMaxJ_map_injective m.embedding m.embedding_injective,
    SymmetricFourWreath.elementary_thompson]
  rfl

theorem elementary_thompson_sup : Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) =
    m.elementaryGroup true true ⊔ m.B := by
  rw [m.elementary_thompson]
  change SymmetricFourWreath.J.map m.embedding = _
  rw [J_eq_sup,Subgroup.map_sup]
  rfl

end CFSG.Quasithin.Chapter13.Section09.Marking
