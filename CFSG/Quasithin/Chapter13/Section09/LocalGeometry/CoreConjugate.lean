module
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Conjugate
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Core

/-!
# The original marked conjugate in Q\Z

Transport the explicit local conjugator into G. This discharges the marked
singular-vector input in source 13.9.8(1), printed p.972 (PDF p.989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem exists_core_conjugate_z : ∃a:G,a∈m.core ∧ a∉zpowers m.z ∧ IsConj m.z a := by
  obtain ⟨a,ha,hn,hconj⟩ := SymmetricFourWreath.core_conjugate_z
  refine ⟨m.sylowModelEmbedding a,mem_map_of_mem _ ha,?_,?_⟩
  · rw [←m.sylowModelEmbedding_center,←MonoidHom.map_zpowers,
      mem_map_iff_mem m.sylowModelEmbedding_injective]
    exact hn
  · obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    apply isConj_iff.mpr
    refine ⟨m.embedding g,?_⟩
    change m.embedding g * m.embedding SymmetricFourWreath.z * (m.embedding g)⁻¹=
      m.embedding (sylowEmbedding a)
    rw [←map_inv,←map_mul,←map_mul,hg]
end CFSG.Quasithin.Chapter13.Section09.Marking
