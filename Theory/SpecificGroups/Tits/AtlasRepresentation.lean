module

public import Theory.SpecificGroups.Tits.AtlasParrottGenerators

/-!
# Parrott's presentation in the ATLAS permutation action

The assignment in `AtlasParrottGenerators` satisfies the 37 relations from
Parrott, “A Characterization of the Tits’ Simple Group” (1972), p. 683,
as transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`.
Each relation is checked pointwise by kernel reduction. The universal
property of the presented group then gives a homomorphism to permutations
of 1600 letters. Two further pointwise certificates exhibit the ATLAS
standard generators in its range.

This construction requires neither faithfulness nor finiteness of the
presented group, and is independent of the nonsolvable-subgroup witness.
-/

namespace Tits

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_r1 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_r1) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_r8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_r8) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s1 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s1) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s2 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s2) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s4) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s6 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s6) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s8) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s3) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s5 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s5) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_i_s7 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .i_s7) = 1 := by
  simp only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_ii_s1_s2 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .ii_s1_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_ii_s1_s3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .ii_s1_s3) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_ii_s1_s5 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .ii_s1_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iii_s1_s6 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iii_s1_s6) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iii_s1_s7 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iii_s1_s7) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iii_s1_s8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iii_s1_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iv_s2_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iv_s2_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iv_s2_s6 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iv_s2_s6) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iv_s2_s8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iv_s2_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_iv_s7_s2 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .iv_s7_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR5, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_v_s7_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .v_s7_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_v_s3_s5 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .v_s3_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_v_s5_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .v_s5_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vi_r1_r8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vi_r1_r8) = 1 := by
  simp only [parrottRelator, map_mul, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vi_s1_r1 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vi_s1_r1) = 1 := by
  simp only [parrottRelator, map_mul, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vi_r8_s8 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vi_r8_s8) = 1 := by
  simp only [parrottRelator, map_mul, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vii_s2 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vii_s2) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vii_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vii_s4) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vii_s5 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vii_s5) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vii_s3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vii_s3) = 1 := by
  simp only [parrottRelator, parrottR3, parrottR7, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_vii_r3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .vii_r3) = 1 := by
  simp only [parrottRelator, parrottR3, parrottR7, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_s2 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_s2) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_s4 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_s4) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_s1 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_s1) = 1 := by
  simp only [parrottRelator, parrottR3, parrottR7, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_s7 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_s7) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_s3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_s3) = 1 := by
  simp only [parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlas_relation_viii_r3 :
    FreeGroup.lift atlasParrottGenerator (parrottRelator .viii_r3) = 1 := by
  simp only [parrottRelator, parrottR3, parrottR5, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]
  apply Equiv.ext
  decide +kernel

/-- All 37 original Parrott relators hold in the concrete ATLAS assignment. -/
public theorem atlasParrottGenerator_satisfies_relations :
    SatisfiesParrottRelations atlasParrottGenerator := by
  intro i
  cases i with
  | i_r1 => exact atlas_relation_i_r1
  | i_r8 => exact atlas_relation_i_r8
  | i_s1 => exact atlas_relation_i_s1
  | i_s2 => exact atlas_relation_i_s2
  | i_s4 => exact atlas_relation_i_s4
  | i_s6 => exact atlas_relation_i_s6
  | i_s8 => exact atlas_relation_i_s8
  | i_s3 => exact atlas_relation_i_s3
  | i_s5 => exact atlas_relation_i_s5
  | i_s7 => exact atlas_relation_i_s7
  | ii_s1_s2 => exact atlas_relation_ii_s1_s2
  | ii_s1_s3 => exact atlas_relation_ii_s1_s3
  | ii_s1_s5 => exact atlas_relation_ii_s1_s5
  | iii_s1_s6 => exact atlas_relation_iii_s1_s6
  | iii_s1_s7 => exact atlas_relation_iii_s1_s7
  | iii_s1_s8 => exact atlas_relation_iii_s1_s8
  | iv_s2_s4 => exact atlas_relation_iv_s2_s4
  | iv_s2_s6 => exact atlas_relation_iv_s2_s6
  | iv_s2_s8 => exact atlas_relation_iv_s2_s8
  | iv_s7_s2 => exact atlas_relation_iv_s7_s2
  | v_s7_s4 => exact atlas_relation_v_s7_s4
  | v_s3_s5 => exact atlas_relation_v_s3_s5
  | v_s5_s4 => exact atlas_relation_v_s5_s4
  | vi_r1_r8 => exact atlas_relation_vi_r1_r8
  | vi_s1_r1 => exact atlas_relation_vi_s1_r1
  | vi_r8_s8 => exact atlas_relation_vi_r8_s8
  | vii_s2 => exact atlas_relation_vii_s2
  | vii_s4 => exact atlas_relation_vii_s4
  | vii_s5 => exact atlas_relation_vii_s5
  | vii_s3 => exact atlas_relation_vii_s3
  | vii_r3 => exact atlas_relation_vii_r3
  | viii_s2 => exact atlas_relation_viii_s2
  | viii_s4 => exact atlas_relation_viii_s4
  | viii_s1 => exact atlas_relation_viii_s1
  | viii_s7 => exact atlas_relation_viii_s7
  | viii_s3 => exact atlas_relation_viii_s3
  | viii_r3 => exact atlas_relation_viii_r3

/-- The homomorphism from Parrott's presented group into the ATLAS action. -/
public def parrottAtlasRepresentation : ParrottGroup →* Equiv.Perm (Fin 1600) :=
  parrottLift atlasParrottGenerator atlasParrottGenerator_satisfies_relations

private def atlasAWord {G : Type*} [Group G] (g : ParrottGenerator → G) : G :=
  (g .s2)⁻¹ * g .r1 * (g .s7)⁻¹ * g .r1 * g .s3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlasAWord_certificate :
    atlasAWord atlasParrottGenerator = atlasA := by
  apply Equiv.ext
  decide +kernel

/-- The ATLAS standard generator `a` lies in the representation's range. -/
public theorem atlasA_mem_parrottAtlasRepresentation_range :
    atlasA ∈ parrottAtlasRepresentation.range := by
  refine ⟨atlasAWord parrottGenerator, ?_⟩
  change parrottLift atlasParrottGenerator atlasParrottGenerator_satisfies_relations
    (atlasAWord parrottGenerator) = atlasA
  simpa only [atlasAWord, map_mul, map_inv, parrottLift_generator]
    using atlasAWord_certificate

private def atlasBWord {G : Type*} [Group G] (g : ParrottGenerator → G) : G :=
  g .s8 * g .s3 * g .r8 * g .r1 * (g .s7)⁻¹ * (g .s3)⁻¹ * (g .s2)⁻¹ *
    (g .s8)⁻¹ * (g .r8)⁻¹ * (g .r1)⁻¹ * g .r8 * g .r1 * (g .s3)⁻¹ * (g .s7)⁻¹ *
    (g .r8)⁻¹ * (g .s8)⁻¹ * g .s5 * (g .r1)⁻¹ * g .r8 * g .s8 * g .r8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem atlasBWord_certificate :
    atlasBWord atlasParrottGenerator = atlasB := by
  apply Equiv.ext
  decide +kernel

/-- The ATLAS standard generator `b` lies in the representation's range. -/
public theorem atlasB_mem_parrottAtlasRepresentation_range :
    atlasB ∈ parrottAtlasRepresentation.range := by
  refine ⟨atlasBWord parrottGenerator, ?_⟩
  change parrottLift atlasParrottGenerator atlasParrottGenerator_satisfies_relations
    (atlasBWord parrottGenerator) = atlasB
  simpa only [atlasBWord, map_mul, map_inv, parrottLift_generator]
    using atlasBWord_certificate

/-- Parrott's presentation has a permutation representation whose image contains
both verified ATLAS standard generators. -/
public theorem exists_parrott_atlas_representation :
    ∃ f : ParrottGroup →* Equiv.Perm (Fin 1600),
      atlasA ∈ f.range ∧ atlasB ∈ f.range :=
  ⟨parrottAtlasRepresentation, atlasA_mem_parrottAtlasRepresentation_range,
    atlasB_mem_parrottAtlasRepresentation_range⟩

end Tits
