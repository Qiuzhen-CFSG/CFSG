module

public import Theory.SpecificGroups.Tits.Atlas1600ParrottData

/-!
# Certificates for the Parrott generators

The kernel checks concrete words witnessing Atlas membership, each of Parrott's
37 original relations, and words recovering the two Atlas generators. The
relations are taken directly from `Presentation.lean`; no reduced presentation
or GAP assertion is used as a proof. The word witnesses were found using GAP
coset actions and Tietze transformations of the source on Parrott (1972), p. 683.
-/

namespace Tits.Atlas1600ParrottData

set_option maxRecDepth 20000

private theorem r1_eq_atlas : r1Perm = atlas1600A := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem b_eq_atlas : bPerm = atlas1600B := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r1_mem : r1Perm ∈ atlas1600Subgroup := by
  rw [r1_eq_atlas]
  exact atlas1600A_mem

private theorem b_mem : bPerm ∈ atlas1600Subgroup := by
  rw [b_eq_atlas]
  exact atlas1600B_mem

private theorem r8_word : r8Perm =
    r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm⁻¹ := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r8_mem : r8Perm ∈ atlas1600Subgroup := by
  rw [r8_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem

private theorem s5_word : s5Perm =
    bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ * r1Perm * bPerm⁻¹ := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s5_mem : s5Perm ∈ atlas1600Subgroup := by
  rw [s5_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem

private theorem s1_word : s1Perm =
    r1Perm * s5Perm⁻¹ * r1Perm * s5Perm * r1Perm := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s1_mem : s1Perm ∈ atlas1600Subgroup := by
  rw [s1_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem

private theorem s3_word : s3Perm =
    r8Perm * s5Perm⁻¹ * r1Perm * r8Perm * s5Perm * r8Perm * r1Perm * s5Perm * r8Perm := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s3_mem : s3Perm ∈ atlas1600Subgroup := by
  rw [s3_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem

private theorem s7_word : s7Perm =
    r8Perm * r1Perm * r8Perm * s5Perm⁻¹ * r8Perm * r1Perm * s5Perm * r8Perm := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s7_mem : s7Perm ∈ atlas1600Subgroup := by
  rw [s7_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem
    | exact s3_mem

private theorem s2_word : s2Perm =
    s1Perm⁻¹ * (r8Perm * (s1Perm * s5Perm ^ 2) * r8Perm) * (s3Perm ^ 2)⁻¹ := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s2_mem : s2Perm ∈ atlas1600Subgroup := by
  rw [s2_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem
    | exact s3_mem
    | exact s7_mem

private theorem s4_word : s4Perm =
    (s7Perm⁻¹ * s2Perm⁻¹ * s7Perm * s2Perm) * (s1Perm * s5Perm ^ 2)⁻¹ := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s4_mem : s4Perm ∈ atlas1600Subgroup := by
  rw [s4_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem
    | exact s3_mem
    | exact s7_mem
    | exact s2_mem

private theorem s6_word : s6Perm =
    r1Perm * s4Perm * r1Perm := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s6_mem : s6Perm ∈ atlas1600Subgroup := by
  rw [s6_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem
    | exact s3_mem
    | exact s7_mem
    | exact s2_mem
    | exact s4_mem

private theorem s8_word : s8Perm =
    r1Perm * s2Perm * r1Perm := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem s8_mem : s8Perm ∈ atlas1600Subgroup := by
  rw [s8_word]
  with_reducible repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | exact r1_mem
    | exact b_mem
    | exact r8_mem
    | exact s5_mem
    | exact s1_mem
    | exact s3_mem
    | exact s7_mem
    | exact s2_mem
    | exact s4_mem
    | exact s6_mem

public theorem permutation_mem (i : ParrottGenerator) : permutation i ∈ atlas1600Subgroup := by
  cases i
  · exact r1_mem
  · exact r8_mem
  · exact s1_mem
  · exact s2_mem
  · exact s3_mem
  · exact s4_mem
  · exact s5_mem
  · exact s6_mem
  · exact s7_mem
  · exact s8_mem

-- The same unfolding list handles all 37 source equations.
section
set_option linter.unusedSimpArgs false

private theorem relation_i_r1 : FreeGroup.lift permutation (parrottRelator .i_r1) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_r8 : FreeGroup.lift permutation (parrottRelator .i_r8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s1 : FreeGroup.lift permutation (parrottRelator .i_s1) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s2 : FreeGroup.lift permutation (parrottRelator .i_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s4 : FreeGroup.lift permutation (parrottRelator .i_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s6 : FreeGroup.lift permutation (parrottRelator .i_s6) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s8 : FreeGroup.lift permutation (parrottRelator .i_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s3 : FreeGroup.lift permutation (parrottRelator .i_s3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s5 : FreeGroup.lift permutation (parrottRelator .i_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_i_s7 : FreeGroup.lift permutation (parrottRelator .i_s7) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_ii_s1_s2 : FreeGroup.lift permutation (parrottRelator .ii_s1_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_ii_s1_s3 : FreeGroup.lift permutation (parrottRelator .ii_s1_s3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_ii_s1_s5 : FreeGroup.lift permutation (parrottRelator .ii_s1_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iii_s1_s6 : FreeGroup.lift permutation (parrottRelator .iii_s1_s6) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iii_s1_s7 : FreeGroup.lift permutation (parrottRelator .iii_s1_s7) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iii_s1_s8 : FreeGroup.lift permutation (parrottRelator .iii_s1_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iv_s2_s4 : FreeGroup.lift permutation (parrottRelator .iv_s2_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iv_s2_s6 : FreeGroup.lift permutation (parrottRelator .iv_s2_s6) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iv_s2_s8 : FreeGroup.lift permutation (parrottRelator .iv_s2_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_iv_s7_s2 : FreeGroup.lift permutation (parrottRelator .iv_s7_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_v_s7_s4 : FreeGroup.lift permutation (parrottRelator .v_s7_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_v_s3_s5 : FreeGroup.lift permutation (parrottRelator .v_s3_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_v_s5_s4 : FreeGroup.lift permutation (parrottRelator .v_s5_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vi_r1_r8 : FreeGroup.lift permutation (parrottRelator .vi_r1_r8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vi_s1_r1 : FreeGroup.lift permutation (parrottRelator .vi_s1_r1) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vi_r8_s8 : FreeGroup.lift permutation (parrottRelator .vi_r8_s8) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vii_s2 : FreeGroup.lift permutation (parrottRelator .vii_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vii_s4 : FreeGroup.lift permutation (parrottRelator .vii_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vii_s5 : FreeGroup.lift permutation (parrottRelator .vii_s5) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vii_s3 : FreeGroup.lift permutation (parrottRelator .vii_s3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_vii_r3 : FreeGroup.lift permutation (parrottRelator .vii_r3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_s2 : FreeGroup.lift permutation (parrottRelator .viii_s2) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_s4 : FreeGroup.lift permutation (parrottRelator .viii_s4) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_s1 : FreeGroup.lift permutation (parrottRelator .viii_s1) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_s7 : FreeGroup.lift permutation (parrottRelator .viii_s7) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_s3 : FreeGroup.lift permutation (parrottRelator .viii_s3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem relation_viii_r3 : FreeGroup.lift permutation (parrottRelator .viii_r3) = 1 := by
  simp only [parrottRelator, parrottCommutator, parrottR3, parrottR5, parrottR7,
    map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, permutation]
  apply Equiv.ext
  apply allFin
  decide +kernel

end

/-- Every original Parrott relator evaluates to the identity. -/
public theorem relations : SatisfiesParrottRelations permutation := by
  intro i
  cases i
  · exact relation_i_r1
  · exact relation_i_r8
  · exact relation_i_s1
  · exact relation_i_s2
  · exact relation_i_s4
  · exact relation_i_s6
  · exact relation_i_s8
  · exact relation_i_s3
  · exact relation_i_s5
  · exact relation_i_s7
  · exact relation_ii_s1_s2
  · exact relation_ii_s1_s3
  · exact relation_ii_s1_s5
  · exact relation_iii_s1_s6
  · exact relation_iii_s1_s7
  · exact relation_iii_s1_s8
  · exact relation_iv_s2_s4
  · exact relation_iv_s2_s6
  · exact relation_iv_s2_s8
  · exact relation_iv_s7_s2
  · exact relation_v_s7_s4
  · exact relation_v_s3_s5
  · exact relation_v_s5_s4
  · exact relation_vi_r1_r8
  · exact relation_vi_s1_r1
  · exact relation_vi_r8_s8
  · exact relation_vii_s2
  · exact relation_vii_s4
  · exact relation_vii_s5
  · exact relation_vii_s3
  · exact relation_vii_r3
  · exact relation_viii_s2
  · exact relation_viii_s4
  · exact relation_viii_s1
  · exact relation_viii_s7
  · exact relation_viii_s3
  · exact relation_viii_r3

/-- The Atlas involution is a Parrott generator. -/
public theorem atlasA_word : atlas1600A = permutation .r1 := r1_eq_atlas.symm

/-- A word in the Parrott images recovers the second Atlas generator. -/
public theorem atlasB_word : atlas1600B =
    (permutation .s3)⁻¹ * (permutation .s3)⁻¹ * (permutation .s6)⁻¹ * (permutation .s5) * (permutation .s3)⁻¹ * (permutation .r1) * (permutation .s8) * (permutation .r8) * (permutation .r1) * (permutation .r8) * (permutation .r1) * (permutation .s7) * (permutation .s7) * (permutation .r8)⁻¹ * (permutation .s7) * (permutation .r1)⁻¹ * (permutation .s5) := by
  rw [← b_eq_atlas]
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.Atlas1600ParrottData
