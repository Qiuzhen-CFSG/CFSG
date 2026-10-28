module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Data
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwoEnumeration

/-!
# Soundness of the double-coset witness test

The packed generators equal the original Parrott permutations. All have fourth
power one, so three forward applications implement a negative letter. The
checker therefore compares actual group elements at a certified permutation
base. Its equality yields the required factorization with both factors in the
marked Sylow subgroup.

Source: Parrott (1972), section 5, p.683; the published eighteen words in
`Representatives` and the Atlas Sylow normal-form certificate.
-/

namespace Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Theory.GroupTheory.CosetEnumeration OuterOddSubgroups.OverlapCentralizers

private theorem packed_code (a : ParrottGenerator) :
    Packed.perm (code a) = Atlas1600ParrottData.permutation a := by
  cases a <;> simp [Packed.perm_eq, Packed.generator, code, Atlas1600ParrottData.permutation]

private theorem generator_fourth (a : ParrottGenerator) :
    Atlas1600ParrottData.permutation a ^ 4 = 1 := by
  cases a
  case r1 =>
    have h : Atlas1600ParrottData.permutation .r1 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_r1
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case r8 =>
    have h : Atlas1600ParrottData.permutation .r8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_r8
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s1 =>
    have h : Atlas1600ParrottData.permutation .s1 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s1
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s2 =>
    have h : Atlas1600ParrottData.permutation .s2 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s2
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s3 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s3
  case s4 =>
    have h : Atlas1600ParrottData.permutation .s4 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s4
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s5 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s5
  case s6 =>
    have h : Atlas1600ParrottData.permutation .s6 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s6
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s7 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s7
  case s8 =>
    have h : Atlas1600ParrottData.permutation .s8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s8
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, h, one_pow]

private theorem fastEval_eq (w : Word ParrottGenerator) :
    fastEval w = eval Atlas1600ParrottData.permutation w := by
  unfold fastEval eval
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, letterValue, packed_code]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact generator_fourth a
  · simp only [↓reduceIte, letterValue, packed_code]

private theorem mapped_eval (w : Word ParrottGenerator) :
    (eval atlas1600ParrottAssignment w).val = eval Atlas1600ParrottData.permutation w := by
  change atlas1600Subgroup.subtype (eval atlas1600ParrottAssignment w) = _
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b
  · change (atlas1600ParrottAssignment a).val⁻¹ = _
    rw [atlas1600ParrottAssignment_val]
    rfl
  · exact atlas1600ParrottAssignment_val a

private theorem fastNormalForm_eq (n : Fin 2048) :
    fastNormalForm n = (atlas1600SylowTwoNormalForm n).val := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, atlas1600SylowTwoNormalForm_val]

private theorem positiveWord_eq (w : List ParrottGenerator) :
    (w.map fun a => Packed.perm (code a)).prod =
      ((w.map atlas1600ParrottAssignment).prod).val := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change Packed.perm (code a) * (w.map fun b => Packed.perm (code b)).prod =
      (atlas1600ParrottAssignment a).val * ((w.map atlas1600ParrottAssignment).prod).val
    rw [ih, packed_code, atlas1600ParrottAssignment_val]

private theorem fastRep_eq (k : Fin 18) : fastRep k = (doubleCosetRep k).val :=
  positiveWord_eq (doubleCosetWord k)

/-- A successful base-point check is an equality of actual Atlas elements. -/
public theorem test_sound (w : Word ParrottGenerator) (j : Fin 5) (c : Nat)
    (h : test w j c = true) :
    (atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1) ^ j.val *
      eval atlas1600ParrottAssignment w =
      atlas1600SylowTwoNormalForm (witnessLeft c) * doubleCosetRep (witnessRep c) *
        atlas1600SylowTwoNormalForm (witnessRight c) := by
  have hv : (atlas1600ParrottAssignment .s1).val *
      (atlas1600ParrottAssignment .r1).val = Packed.perm 2 * Packed.perm 0 := by
    simp [Packed.perm_eq, Packed.generator, atlas1600ParrottAssignment_val,
      Atlas1600ParrottData.permutation]
  have hg : ((atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1) ^ j.val *
      eval atlas1600ParrottAssignment w).val =
      (Packed.perm 2 * Packed.perm 0) ^ j.val * fastEval w := by
    change ((atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val) ^
      j.val * (eval atlas1600ParrottAssignment w).val = _
    rw [hv, mapped_eval, fastEval_eq]
  have hh : (atlas1600SylowTwoNormalForm (witnessLeft c) * doubleCosetRep (witnessRep c) *
      atlas1600SylowTwoNormalForm (witnessRight c)).val =
      fastNormalForm (witnessLeft c) * fastRep (witnessRep c) *
        fastNormalForm (witnessRight c) := by
    change (atlas1600SylowTwoNormalForm (witnessLeft c)).val *
      (doubleCosetRep (witnessRep c)).val * (atlas1600SylowTwoNormalForm (witnessRight c)).val = _
    rw [fastNormalForm_eq, fastRep_eq, fastNormalForm_eq]
  simp only [test, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨h0, h1⟩, h2⟩
  apply threePoint_ext
  · simpa only [hg, hh] using h0
  · simpa only [hg, hh] using h1
  · simpa only [hg, hh] using h2

end Tits.ConverseLocalCoverage.DoubleCosetCertificate
