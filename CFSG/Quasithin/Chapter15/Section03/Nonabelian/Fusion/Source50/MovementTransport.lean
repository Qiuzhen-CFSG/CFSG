module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport

/-!
# The literal displacement subgroup in the orthogonal coordinates

The coordinate embedding identifies action displacements with ambient
commutators. Thus a calculation in the four-dimensional actor applies to
[U,V] for the actual U and V, with the source's conjugation convention.

Source: Aschbacher–Smith, 15.3.53(2), printed p.1146.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction
variable {G : Type*} [Group G] {M V : Subgroup G}

/-- Transport the generated displacement subgroup through the specified
coordinate embedding. -/
theorem NaturalOrthogonalAction.map_displacement (d : NaturalOrthogonalAction M V)
    (U : Subgroup G) (hUM : U ≤ M) :
    (closure {w : OrthogonalVector | ∃ r ∈ d.image U, ∃ v : OrthogonalVector,
      r • v * v⁻¹ = w}).map d.vectorEmbedding = ⁅U,V⁆ := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨_,⟨u,hu,rfl⟩,v,rfl⟩
    change d.vectorEmbedding (d.actor u • v * v⁻¹) ∈ ⁅U,V⁆
    rw [map_mul,map_inv,d.vectorEmbedding_conjugate]
    have hv : d.vectorEmbedding v ∈ V :=
      d.vectorEmbedding_range.le ⟨v,rfl⟩
    exact commutator_mem_commutator hu hv
  · apply commutator_le.mpr
    intro u hu v hv
    obtain ⟨w,rfl⟩ := (d.vectorEmbedding_range.symm ▸ hv : v ∈ d.vectorEmbedding.range)
    refine ⟨d.actor ⟨u,hUM hu⟩ • w * w⁻¹,
      subset_closure ⟨_,mem_map_of_mem d.actor hu,w,rfl⟩,?_⟩
    rw [map_mul,map_inv,d.vectorEmbedding_conjugate]
    rfl

end CFSG.Quasithin.Chapter15.Section03
