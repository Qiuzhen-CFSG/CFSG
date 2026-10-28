module

public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.QuasithinBasic

/-!
# Transport of maximal two-local overgroups

An isomorphism identifies the maximal two-local overgroups of a subgroup
with those of its image. In particular their number is independent of the
chosen Sylow two-subgroup. This transports the multiple-overgroup standing
hypothesis when a local proof replaces its Sylow subgroup.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- The maximal two-local overgroup family is transported by an isomorphism. -/
theorem maximalTwoLocalOvergroups_map (e : G ≃* H) (U : Subgroup G) :
    maximalTwoLocalOvergroups (U.map e.toMonoidHom) =
      (fun M : Subgroup G => M.map e.toMonoidHom) '' maximalTwoLocalOvergroups U := by
  ext N
  constructor
  · intro hN
    refine ⟨N.map e.symm.toMonoidHom, ⟨isMaximalTwoLocal_map e.symm hN.1, ?_⟩, ?_⟩
    · simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hN.2
    · simp [map_map]
  · rintro ⟨M, hM, rfl⟩
    exact ⟨isMaximalTwoLocal_map e hM.1, map_mono hM.2⟩

/-- The number of maximal two-local overgroups is invariant under isomorphism. -/
theorem maximalTwoLocalOvergroups_ncard_map (e : G ≃* H) (U : Subgroup G) :
    (maximalTwoLocalOvergroups (U.map e.toMonoidHom)).ncard =
      (maximalTwoLocalOvergroups U).ncard := by
  rw [maximalTwoLocalOvergroups_map]
  exact Set.ncard_image_of_injective _ (map_injective e.injective)

/-- All Sylow two-subgroups have the same number of maximal two-local overgroups. -/
theorem maximalTwoLocalOvergroups_ncard_sylow [Finite G] (S T : Sylow 2 G) :
    (maximalTwoLocalOvergroups (S : Subgroup G)).ncard =
      (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have he : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) := by
    change (g • S : Sylow 2 G).toSubgroup = T.toSubgroup
    rw [hg]
  rw [← he, maximalTwoLocalOvergroups_ncard_map]

end Theory.GroupTheory
