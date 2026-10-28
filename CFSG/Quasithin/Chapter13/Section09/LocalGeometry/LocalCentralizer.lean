module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.ZCentralizer
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Core

/-!
# The original local centralizer of z

Transport the wreath calculation through the actual marked embedding. The
centralizer in the supplied maximal two-local M is precisely the original
Sylow subgroup T. This discharges the local identity in 13.9.5 and 13.9.8(2),
printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem local_centralizer_z :
    centralizer ({m.z}:Set G) ⊓ d.M=(d.T:Subgroup G) := by
  apply le_antisymm
  · rintro x ⟨hx,hM⟩
    rw [←m.range_embedding] at hM
    obtain ⟨w,rfl⟩ := hM
    rw [←m.image_standardSylow]
    refine mem_map_of_mem _ ?_
    rw [←SymmetricFourWreath.centralizer_z,mem_centralizer_singleton_iff]
    apply m.embedding_injective
    simpa only [map_mul, z] using (mem_centralizer_singleton_iff.mp hx)
  · exact le_inf m.z_central_sylow d.sylow_le
end CFSG.Quasithin.Chapter13.Section09.Marking
