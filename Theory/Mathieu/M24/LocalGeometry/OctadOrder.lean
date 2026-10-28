module

public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Theory.Mathieu.M24.Properties.Transitivity
public import Theory.GroupTheory.SteinerSystem.Completion

/-!
# Orders of octad stabilizers in the native Mathieu group

Five-transitivity transports five-point subsets, and unique Witt-design
extension transports their octads. The orbit of each octad is therefore
the certified set of 759 blocks. Orbit--stabilizer gives index 759 and
order 322560, using the existing order of the actual W24 automorphism group.

This is the order calculation for the E16-by-A8 local subgroup in GLS,
volume 3, Table 5.3e. The group structure and the placement of arbitrary
Sylow overgroups require separate proofs.
-/

public section

namespace Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

private theorem smul_octad_mem (g : M24) {O : Finset (Fin 24)} (hO : O ∈ m24Blocks) :
    g • O ∈ m24Blocks := by
  have h := (mem_M24_iff g.val).mp g.property
  change g.val • O ∈ (m24Blocks : Set (Finset (Fin 24)))
  rw [← h]
  exact Set.smul_mem_smul_set hO

/-- Five-transitivity transports octads because a five-set determines its block. -/
theorem exists_smul_octad_eq (O P : Octad) : ∃ g : M24, g • O.val = P.val := by
  classical
  let eO : Fin 8 ≃ O.val := (Finset.equivFinOfCardEq (m24Blocks_card _ O.property)).symm
  let eP : Fin 8 ≃ P.val := (Finset.equivFinOfCardEq (m24Blocks_card _ P.property)).symm
  let j : Fin 5 ↪ Fin 8 := Fin.castLEEmb (by decide)
  let a : Fin 5 ↪ Fin 24 := (j.trans eO.toEmbedding).trans (Function.Embedding.subtype _)
  let b : Fin 5 ↪ Fin 24 := (j.trans eP.toEmbedding).trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp m24_isFivePretransitive) a b
  have happ (i : Fin 5) : g • a i = b i :=
    congrArg (fun f : Fin 5 ↪ Fin 24 => f i) hg
  refine ⟨g, m24WittDesign.block_eq_of_subset (S := Finset.univ.image b) ?_ ?_ ?_ ?_ ?_⟩
  · rw [Finset.card_image_of_injective _ b.injective, Finset.card_univ, Fintype.card_fin]
  · rw [m24WittDesign_blocks]
    exact smul_octad_mem g O.property
  · rw [m24WittDesign_blocks]
    exact P.property
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [← happ i]
    exact Finset.smul_mem_smul_finset (eO (j i)).property
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (eP (j i)).property

/-- The orbit consists of all certified octads. -/
theorem orbit_octad (O : Octad) :
    MulAction.orbit M24 O.val = (m24Blocks : Set (Finset (Fin 24))) := by
  ext P
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact smul_octad_mem g O.property
  · intro hP
    exact exists_smul_octad_eq O ⟨P, hP⟩

/-- Every octad stabilizer has odd index 759. -/
theorem octadStabilizer_index (O : Octad) : (octadStabilizer O).index = 759 := by
  rw [octadStabilizer, MulAction.index_stabilizer, orbit_octad,
    Set.ncard_coe_finset, m24Blocks_cardinality]

/-- Every octad stabilizer has order 322560. -/
theorem octadStabilizer_card (O : Octad) : Nat.card (octadStabilizer O) = 322560 := by
  have h := Subgroup.card_mul_index (octadStabilizer O)
  rw [octadStabilizer_index, m24_order] at h
  omega

end Sporadic.Mathieu.M24LocalGeometry
