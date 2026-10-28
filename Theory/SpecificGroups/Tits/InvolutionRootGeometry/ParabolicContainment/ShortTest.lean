module

public import Theory.SpecificGroups.Tits.R1Certificate.Data
public import Theory.SpecificGroups.Tits.Atlas1600ParrottCertificate
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.List.FinRange
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Short-root tests on the certified ambient coset words

An element has the form s (s₁r₁)ʲ w, with s in the marked Sylow subgroup,
j < 5 and w a stored R₁ coset representative. If it centralizes s₄, the
suffix sends s₄ to one of its four Sylow conjugates. Two point comparisons
exclude all suffixes not visibly in the second parabolic.

The executable test evaluates only the needed points with the existing
kernel-certified packed maps. Its equality with evaluation of the original
Parrott permutations is proved here; the complete finite check is separate.
Source: Parrott (1972), §5, p.683, and the certified ambient R₁ cover.
-/

public section

open Theory.GroupTheory.CosetEnumeration
namespace Tits.InvolutionRootGeometry.ParabolicContainment.Certificate
open Atlas1600ParrottData OuterOddSubgroups.OverlapCentralizers

@[expose] def code : ParrottGenerator → Fin 10
  | .r1 => 0 | .r8 => 1 | .s1 => 2 | .s2 => 3 | .s3 => 4
  | .s4 => 5 | .s5 => 6 | .s6 => 7 | .s7 => 8 | .s8 => 9

@[expose] def fastEval (w : Word ParrottGenerator) : Equiv.Perm (Fin 1600) :=
  (w.map fun a => if a.2 then Packed.perm (code a.1) else Packed.perm (code a.1) ^ 3).prod

@[expose] def orbitPerm (k : Fin 4) : Equiv.Perm (Fin 1600) :=
  let c := ![1, s3Perm, s7Perm, s7Perm * s3Perm] k
  c * s4Perm * c⁻¹

@[expose] def inSecond (w : Word ParrottGenerator) (j : Fin 5) : Bool :=
  j == 0 && w.all (fun a => a.1 != .r1)

@[expose] def fastOrbitPerm (k : Fin 4) : Equiv.Perm (Fin 1600) :=
  ![Packed.perm 5,
    Packed.perm 4 * Packed.perm 5 * Packed.perm 4 ^ 3,
    Packed.perm 8 * Packed.perm 5 * Packed.perm 8 ^ 3,
    Packed.perm 8 * Packed.perm 4 * Packed.perm 5 * Packed.perm 4 ^ 3 * Packed.perm 8 ^ 3] k

@[expose] def separates (w : Word ParrottGenerator) (j : Fin 5) (k : Fin 4) : Bool :=
  let v := (Packed.perm 2 * Packed.perm 0) ^ j.val * fastEval w
  (v (Packed.perm 5 0) != fastOrbitPerm k (v 0)) ||
    (v (Packed.perm 5 1) != fastOrbitPerm k (v 1))

@[expose] def test (w : Word ParrottGenerator) : Bool :=
  (List.finRange 5).all fun j =>
    inSecond w j || (List.finRange 4).all (separates w j)

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
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case r8 =>
    have h : Atlas1600ParrottData.permutation .r8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_r8
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s1 =>
    have h : Atlas1600ParrottData.permutation .s1 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s2 =>
    have h : Atlas1600ParrottData.permutation .s2 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s3 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s3
  case s4 =>
    have h : Atlas1600ParrottData.permutation .s4 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s4
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s5 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s5
  case s6 =>
    have h : Atlas1600ParrottData.permutation .s6 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s6
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  case s7 =>
    simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
      using Atlas1600ParrottData.relations .i_s7
  case s8 =>
    have h : Atlas1600ParrottData.permutation .s8 ^ 2 = 1 := by
      simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of]
        using Atlas1600ParrottData.relations .i_s8
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]

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

private theorem generator_inv (a : ParrottGenerator) :
    permutation a ^ 3 = (permutation a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact generator_fourth a

private theorem fastOrbit_eq (k : Fin 4) : fastOrbitPerm k = orbitPerm k := by
  have h3 : s3Perm ^ 3 = s3Perm⁻¹ := generator_inv .s3
  have h7 : s7Perm ^ 3 = s7Perm⁻¹ := generator_inv .s7
  fin_cases k <;>
    simp [fastOrbitPerm, orbitPerm, Packed.perm_eq, Packed.generator, h3, h7, mul_assoc]

theorem separates_eq (w : Word ParrottGenerator) (j : Fin 5) (k : Fin 4) :
    separates w j k =
      (let v := (s1Perm*r1Perm)^j.val * eval permutation w
       (v (s4Perm 0) != orbitPerm k (v 0)) || (v (s4Perm 1) != orbitPerm k (v 1))) := by
  simp [separates, fastOrbit_eq, fastEval_eq, Packed.perm_eq, Packed.generator]

@[expose] def letterPoint (a : Letter ParrottGenerator) (p : Fin 1600) : Fin 1600 :=
  if a.2 then Packed.pointMap (code a.1) p else
    Packed.pointMap (code a.1) (Packed.pointMap (code a.1) (Packed.pointMap (code a.1) p))

@[expose] def wordPoint (w : Word ParrottGenerator) (p : Fin 1600) : Fin 1600 :=
  w.foldr letterPoint p

@[expose] def rotationPoint (j : Fin 5) (p : Fin 1600) : Fin 1600 :=
  (fun p => Packed.pointMap 2 (Packed.pointMap 0 p))^[j.val] p

@[expose] def orbitPoint (k : Fin 4) (p : Fin 1600) : Fin 1600 :=
  let a := Packed.pointMap 4
  let b := Packed.pointMap 8
  let z := Packed.pointMap 5
  ![z p, a (z (a (a (a p)))), b (z (b (b (b p)))),
    b (a (z (a (a (a (b (b (b p))))))))] k

@[expose] def pointSeparates (w : Word ParrottGenerator) (j : Fin 5) (k : Fin 4) : Bool :=
  let v := fun p => rotationPoint j (wordPoint w p)
  (v (Packed.pointMap 5 0) != orbitPoint k (v 0)) ||
    (v (Packed.pointMap 5 1) != orbitPoint k (v 1))

@[expose] def pointTest (w : Word ParrottGenerator) : Bool :=
  (List.finRange 5).all fun j =>
    inSecond w j || (List.finRange 4).all (pointSeparates w j)

private theorem wordPoint_eq (w : Word ParrottGenerator) (p : Fin 1600) :
    wordPoint w p = fastEval w p := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp only [wordPoint, List.foldr_cons, fastEval, List.map_cons, List.prod_cons,
      Equiv.Perm.mul_apply]
    rw [show w.foldr letterPoint p = fastEval w p from ih p]
    cases a with
    | mk a b => cases b <;> rfl

private theorem rotationPoint_eq (j : Fin 5) (p : Fin 1600) :
    rotationPoint j p = ((Packed.perm 2 * Packed.perm 0) ^ j.val) p := by
  change ((Packed.perm 2 * Packed.perm 0) : Equiv.Perm (Fin 1600))^[j.val] p = _
  rw [← Equiv.Perm.coe_pow]

private theorem orbitPoint_eq (k : Fin 4) (p : Fin 1600) :
    orbitPoint k p = fastOrbitPerm k p := by
  fin_cases k <;> rfl

theorem pointSeparates_eq (w : Word ParrottGenerator) (j : Fin 5) (k : Fin 4) :
    pointSeparates w j k = separates w j k := by
  simp only [pointSeparates, orbitPoint_eq, rotationPoint_eq, wordPoint_eq]
  rfl

end Tits.InvolutionRootGeometry.ParabolicContainment.Certificate
