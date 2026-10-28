module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeCoverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Intersections
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Generation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.VertexGeneration

/-!
# The concrete Hall–Janko local A₅ groups and their markings

The literal edge fixer E and the full centralizer K of the fixed dihedral
subgroup are each isomorphic to A₅. Their vertex intersection K ∩ M is the
marked S₃, while K's setwise edge stabilizer is precisely ⟨t⟩. Conjugation by
this fixed reversal is the identity on E. The maps below attach the model
groups to the literal subgroup inclusions, including the common S₃ marking.

The three generation identities for the uniqueness system are exported as
`K_sup_M`, `E_sup_K_inf_M`, and `local_generate`. Only the middle identity
requires `hM : Nat.card M = 2160`; the separate orbit-action calculation
supplies it. All other assertions are unconditional on the actual ATLAS carrier.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2, 47.5 and 47.10,
pp.261, 263, 266–267. The original carrier, endpoints, dihedral marking,
graph, and reversal remain unchanged. No simplicity or order-based
recognition is used. The finite candidates and reproduction scripts live
under `LocalA5/source/`; the companion modules check them in Lean's kernel.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory.GraphUniquenessSystem

/-- The edge model placed in M by the literal inclusion E ≤ M. -/
noncomputable def edgeIntoM : alternatingGroup (Fin 5) →* M :=
  (Subgroup.inclusion (show E ≤ M from inf_le_left)).comp edgeEquiv.symm.toMonoidHom

/-- The vertex-intersection model placed in M by the literal inclusion. -/
noncomputable def vertexIntoM : Equiv.Perm (Fin 3) →* M :=
  (Subgroup.inclusion (show K ⊓ M ≤ M from inf_le_right)).comp vertexEquiv.symm.toMonoidHom

/-- The very same vertex-intersection marking in the local A₅ model. -/
noncomputable def vertexIntoLocal : Equiv.Perm (Fin 3) →* alternatingGroup (Fin 5) :=
  localEquiv.toMonoidHom.comp
    ((Subgroup.inclusion (show K ⊓ M ≤ K from inf_le_left)).comp vertexEquiv.symm.toMonoidHom)

theorem edgeIntoM_coe (p : alternatingGroup (Fin 5)) :
    (edgeIntoM p : Carrier) = (edgeEquiv.symm p : Carrier) := by rfl

theorem vertexIntoM_coe (p : Equiv.Perm (Fin 3)) :
    (vertexIntoM p : Carrier) = (vertexEquiv.symm p : Carrier) := by rfl

/-- The two marked maps agree after the literal inclusions into the carrier. -/
theorem vertex_maps_agree (p : Equiv.Perm (Fin 3)) :
    (localEquiv.symm (vertexIntoLocal p) : Carrier) = (vertexIntoM p : Carrier) := by
  change (localEquiv.symm (localEquiv _) : Carrier) = _
  rw [localEquiv.symm_apply_apply]
  rfl

theorem edgeIntoM_rotation : (edgeIntoM EdgeData.model0 : Carrier) = rotation := by
  rw [edgeIntoM_coe, edgeEquiv_symm_coe, edgeHom_model0]

/-- The shared cubic has the chosen model marking on both sides of the inclusion. -/
theorem vertexIntoLocal_modelX : vertexIntoLocal VertexData.modelX = LocalData.model0 := by
  apply localEquiv.symm.injective
  apply Subtype.ext
  rw [vertex_maps_agree, vertexIntoM_coe, vertexEquiv_symm_coe, vertexHom_modelX,
    localEquiv_symm_coe, localHom_model0]

/-- The same compatibility for the fixed inverting involution. -/
theorem vertexIntoLocal_modelS : vertexIntoLocal VertexData.modelS = LocalData.model2 := by
  apply localEquiv.symm.injective
  apply Subtype.ext
  rw [vertex_maps_agree, vertexIntoM_coe, vertexEquiv_symm_coe, vertexHom_modelS,
    localEquiv_symm_coe, localHom_model2]

theorem localEquiv_symm_reversal :
    (localEquiv.symm (LocalData.model0 * (LocalData.model0 * LocalData.model1⁻¹) *
      LocalData.model0⁻¹) : Carrier) = t := by
  rw [localEquiv_symm_coe, map_mul, map_mul, map_mul, map_inv, map_inv,
    localHom_model0, localHom_model1]
  rfl

/-- The reversal's conjugation identity on every element of the edge model. -/
theorem t_conj_edge_model (p : alternatingGroup (Fin 5)) :
    t * (edgeIntoM p : Carrier) * t⁻¹ = (edgeIntoM p : Carrier) :=
  t_conj_of_mem_E (edgeEquiv.symm p).property

/-- Exactly the three local calculations consumed by the concrete system. -/
theorem calculations (hM : Nat.card M = 2160) :
    K ⊔ M = ⊤ ∧ E ⊔ (K ⊓ M) = M ∧
      (K ⊓ edgeStabilizer Carrier base neighbor) ⊔ (K ⊓ M) = K :=
  ⟨K_sup_M, E_sup_K_inf_M hM, local_generate⟩

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
