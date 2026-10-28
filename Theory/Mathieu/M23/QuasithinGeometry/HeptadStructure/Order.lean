module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.Actions
public import Theory.Mathieu.M23.Properties.Order

/-!
# The order of the heptad stabilizer

Four-transitivity and unique heptad extension imply transitivity on the 253
heptads. Orbit--stabilizer therefore gives order 40320 for the chosen heptad
stabilizer. This supplies the upper bound for identifying its kernel and image.

Source: Aschbacher--Smith, §5.2, notation preceding Lemma 5.2.17.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- Every heptad is an M23 translate of the chosen heptad. -/
theorem exists_smul_omega_eq {B : Finset (Fin 23)} (hB : B ∈ m23Blocks) :
    ∃ g : M23, g • omega = B := by
  classical
  let e : Fin 7 ≃ B := (Fintype.equivFinOfCardEq (by
    simpa using m23Blocks_card B hB)).symm
  let j : Fin 4 ↪ Fin 7 := Fin.castLEEmb (by decide)
  let a : Fin 4 ↪ Fin 23 := j.trans label
  let b : Fin 4 ↪ Fin 23 := (j.trans e.toEmbedding).trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp
    m23_isFourPretransitive) a b
  have happ (i : Fin 4) : g • a i = b i :=
    congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  refine ⟨g, heptad_eq_of_four_subset (S := Finset.univ.image b) ?_
    (smul_heptad g omega_mem) hB ?_ ?_⟩
  · rw [Finset.card_image_of_injective _ b.injective, Finset.card_univ, Fintype.card_fin]
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [← happ i]
    apply Finset.smul_mem_smul_finset
    exact (labelEquiv (j i)).property
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (e (j i)).property

/-- The orbit is the certified finite set of all heptads. -/
theorem orbit_omega : MulAction.orbit M23 omega = (m23Blocks : Set (Finset (Fin 23))) := by
  ext B
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact smul_heptad g omega_mem
  · exact exists_smul_omega_eq

/-- The heptad stabilizer has index 253 in M23. -/
theorem heptadStabilizer_index : heptadStabilizer.index = 253 := by
  rw [MulAction.index_stabilizer, orbit_omega, Set.ncard_coe_finset, m23Blocks_cardinality]

set_option maxRecDepth 10000 in
/-- The order needed for the concrete split-extension identification. -/
theorem heptadStabilizer_card : Nat.card heptadStabilizer = 40320 := by
  have h := Subgroup.card_mul_index heptadStabilizer
  rw [heptadStabilizer_index, m23_order] at h
  omega

end Sporadic.Mathieu.M23Geometry
