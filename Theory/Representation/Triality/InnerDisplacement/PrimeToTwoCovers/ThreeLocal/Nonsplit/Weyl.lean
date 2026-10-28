module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit.Raw
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.CorootReflection
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Weyl equations for the algebraic nonsplit triality torus

The prescribed D₄ Coxeter word acts by an explicit permutation on the natural
hyperbolic space. Its cube exchanges the two halves, and its square has order
three and is not diagonal. Faithfulness of the natural action lifts these
calculations to the original Clifford Spin points.

On simple-coroot parameters the Coxeter action commutes with opposition
followed by the graph-field map. It therefore preserves exactly the signed
fixed tuples `(a,b,a⁻ᑫ,aᑫ²)`. The central reflection uses the norm exponent
`q²-q+1`, so the two factors retain their actual orders `q³+1` and `q+1`.
The resulting `weylLaws` supplies all five algebraic inputs of the nonsplit
three-local assembly. No rational descent is assumed, and the proof includes
`q=2` (indeed it works for every natural exponent).

Source: GLS3 §1.12, especially Theorem 1.12.1(h,i,k), and §§2.3–2.4,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`, for the
Weyl calculations supporting §6.1.
-/

@[expose] public section
noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
open Theory.AlgebraicGroup Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration

private theorem coxeter_apply (z : HyperbolicSpace Scalars 4) :
    (naturalAction Scalars coxeter).1 z =
    (![z.1 2, z.1 0, z.2 1, z.2 3], ![z.2 2, z.2 0, z.1 1, z.1 3]) := by
  simp only [coxeter, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
    simpleNormalizer_apply]
  rfl

private theorem cycleWord_apply (z : HyperbolicSpace Scalars 4) :
    (naturalAction Scalars cycleWord).1 z =
    (![z.2 1, z.1 2, z.2 0, z.1 3], ![z.1 1, z.2 2, z.1 0, z.2 3]) := by
  simp only [cycleWord, pow_two, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
    coxeter_apply]
  rfl

private theorem inverterWord_apply (z : HyperbolicSpace Scalars 4) :
    (naturalAction Scalars inverterWord).1 z = (z.2, z.1) := by
  rw [inverterWord, pow_succ, pow_two]
  simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, coxeter_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private def coxeterCoordinates (t : Fin 4 → Scalarsˣ) : Fin 4 → Scalarsˣ :=
  ![t 2 * t 3 * (t 1)⁻¹, t 0 * t 2 * t 3 * (t 1)⁻¹,
    t 0 * t 3 * (t 1)⁻¹, t 0 * t 2 * (t 1)⁻¹]

private def reflectionCoordinates (t : Fin 4 → Scalarsˣ) : Fin 4 → Scalarsˣ :=
  ![t 0, t 0 * t 2 * t 3 * (t 1)⁻¹, t 2, t 3]

private theorem diagonal_coxeterCoordinates (t : Fin 4 → Scalarsˣ) :
    CorootTorus.diagonal Scalars (coxeterCoordinates t) =
      ![CorootTorus.diagonal Scalars t 2, CorootTorus.diagonal Scalars t 0,
        (CorootTorus.diagonal Scalars t 1)⁻¹, (CorootTorus.diagonal Scalars t 3)⁻¹] := by
  funext i
  fin_cases i <;> simp [CorootTorus.diagonal, coxeterCoordinates,
    mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem coxeter_parameter (t : Fin 4 → Scalarsˣ) :
    coxeter * CorootTorus.parameter Scalars t * coxeter⁻¹ =
      CorootTorus.parameter Scalars (coxeterCoordinates t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply naturalAction_injective Scalars
  simp only [map_mul, CorootTorus.naturalAction_parameter]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeter_apply, diagonalAction_spec]
  rw [diagonal_coxeterCoordinates]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp [diagonalAction]

private theorem reflection_parameter (t : Fin 4 → Scalarsˣ) :
    reflectionWord * CorootTorus.parameter Scalars t * reflectionWord⁻¹ =
      CorootTorus.parameter Scalars (reflectionCoordinates t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply naturalAction_injective Scalars
  simp only [map_mul, CorootTorus.naturalAction_parameter]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionWord,
    simpleNormalizer_apply, diagonalAction_spec]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [diagonalAction, CorootTorus.diagonal, reflectionCoordinates, simpleAction,
      mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem inverter_parameter (t : Fin 4 → Scalarsˣ) :
    inverterWord * CorootTorus.parameter Scalars t * inverterWord⁻¹ =
      CorootTorus.parameter Scalars (t⁻¹) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply naturalAction_injective Scalars
  simp only [map_mul, CorootTorus.naturalAction_parameter]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inverterWord_apply, diagonalAction_spec]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [diagonalAction, CorootTorus.diagonal,
      mul_inv_rev, mul_assoc, mul_comm]

private theorem coxeterCoordinates_signedTwist (n : ℕ) (t : Fin 4 → Scalarsˣ) :
    signedTwist n (coxeterCoordinates t) = coxeterCoordinates (signedTwist n t) := by
  funext i
  fin_cases i <;>
    simp [signedTwist, coxeterCoordinates, mul_pow, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm]

private theorem normHom_val (n : ℕ) (a : Large n) :
    (normHom n a : Scalarsˣ) =
      (a : Scalarsˣ) * ((a : Scalarsˣ) ^ (2 ^ n))⁻¹ * (a : Scalarsˣ) ^ ((2 ^ n) ^ 2) := by
  change (a : Scalarsˣ) ^ ((2 ^ n) ^ 2 - 2 ^ n + 1) = _
  rw [pow_succ, pow_sub _ (Nat.le_self_pow (by decide : 2 ≠ 0) (2 ^ n))]
  ac_rfl

/-- The central reflection uses the actual unequal-factor norm. -/
theorem reflectionWord_rawTorus (n : ℕ) (a : Coordinates n) :
    reflectionWord * rawTorus n a * reflectionWord⁻¹ = rawTorus n (reflection n a) := by
  change reflectionWord * CorootTorus.parameter Scalars (expand n a) * reflectionWord⁻¹ =
    CorootTorus.parameter Scalars (expand n (reflection n a))
  rw [reflection_parameter]
  congr 1
  funext i
  fin_cases i <;>
    simp [reflectionCoordinates, expand, reflection, normHom_val,
      mul_comm, mul_left_comm]

/-- The folded Coxeter element preserves the literal signed fixed torus. -/
theorem coxeter_normalizes_rawTorus (n : ℕ) :
    coxeter ∈ Subgroup.normalizer ((rawTorus n).range : Set Ambient) := by
  let : Finite ((rawTorus n).range : Set Ambient) :=
    Finite.of_equiv (Coordinates n) (MonoidHom.ofInjective (rawTorus_injective n)).toEquiv
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := exists_expand_of_signedTwist n (coxeterCoordinates (expand n a)) (by
    rw [coxeterCoordinates_signedTwist, signedTwist_expand])
  refine ⟨b, ?_⟩
  change CorootTorus.parameter Scalars (expand n b) =
    coxeter * CorootTorus.parameter Scalars (expand n a) * coxeter⁻¹
  rw [coxeter_parameter, hb]

/-- Normalization is of the original range, before any rational descent. -/
theorem cycleWord_normalizes_rawTorus (n : ℕ) :
    cycleWord ∈ Subgroup.normalizer ((rawTorus n).range : Set Ambient) :=
  (Subgroup.normalizer ((rawTorus n).range : Set Ambient)).pow_mem
    (coxeter_normalizes_rawTorus n) 2

/-- The opposition word inverts the original coroot product. -/
theorem inverterWord_rawTorus (n : ℕ) (a : Coordinates n) :
    inverterWord * rawTorus n a * inverterWord⁻¹ = (rawTorus n a)⁻¹ := by
  change inverterWord * CorootTorus.parameter Scalars (expand n a) * inverterWord⁻¹ =
    ((CorootTorus.pointHom Scalars) (expand n a))⁻¹
  rw [inverter_parameter]
  exact map_inv (CorootTorus.pointHom Scalars) (expand n a)

/-- A diagonal point cannot move this basis vector to the opposite hyperbolic half. -/
theorem cycleWord_outside_rawTorus (n : ℕ) : cycleWord ∉ (rawTorus n).range := by
  rintro ⟨a, ha⟩
  change CorootTorus.parameter Scalars (expand n a) = cycleWord at ha
  have h := congrArg (fun g : Ambient =>
    ((naturalAction Scalars g).1 (Pi.single 0 1, 0)).2 2) ha
  rw [CorootTorus.naturalAction_parameter, diagonalAction_spec, cycleWord_apply] at h
  norm_num [diagonalAction] at h
  exact zero_ne_one h

/-- The word has order three even at the smallest field parameter. -/
theorem cycleWord_order : orderOf cycleWord = 3 := by
  have hi : inverterWord ^ 2 = 1 := by
    apply naturalAction_injective Scalars
    simp only [pow_two, map_mul, map_one]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, inverterWord_apply,
      Subgroup.coe_one]
    rfl
  apply orderOf_eq_prime
  · convert hi using 1; simp [cycleWord, inverterWord, ← pow_mul]
  · intro h
    exact cycleWord_outside_rawTorus 0 (h ▸ (rawTorus 0).range.one_mem)

/-- All algebraic Weyl laws, with no rational-descent or covering premise. -/
theorem weylLaws (n : ℕ) : WeylLaws n where
  reflection_action := reflectionWord_rawTorus n
  cycle_order := cycleWord_order
  cycle_outside := cycleWord_outside_rawTorus n
  cycle_normalizes := cycleWord_normalizes_rawTorus n
  inverter_action := inverterWord_rawTorus n

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Nonsplit
