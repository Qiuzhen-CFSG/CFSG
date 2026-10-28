module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.Data

/-!
# Complete reconstruction from the shear residue equations

A residue is a linear functional vanishing on the literal thirteen-generator
upper space. The first recovery identity reconstructs an arbitrary parameter
from 63 coordinates, and the second reconstructs every remaining parameter
from one coordinate. A final checked identity identifies its lift with the
existing finalParameter. The source is Kernel/source/generate.py; none of its
numerical assertions are assumed.
-/

@[expose] public section
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates FiniteAlgebra

def BaseChecks : Prop :=
  (∀ t : Fin 2, mulRows (transRows 50 pairingInverseRows) (testIURows.get t) =
    twistedRows t) ∧
  (∀ k : Fin 13, pivotRadicalWords.get k = radicalWord (pivots.get k)) ∧
  (∀ (t : Fin 2) (k : Fin 13),
    (pivotCoefficientWords t).get k = coefficientWord (twistedRows t) (pivots.get k))

def FirstChecks (i : Fin 1212) : Prop :=
  radicalWord (firstPositions.get i) =
    scan (firstCorrections.get i) pivotRadicalWords.toList ∧
  firstEquations.get i = coefficientWord (twistedRows 0) (firstPositions.get i) ^^^
    scan (firstCorrections.get i) (pivotCoefficientWords 0).toList

def firstFree (x : Parameter) (k : Fin 63) : ZMod 2 := x ⟨1212 + k.val, by omega⟩

def firstUnitRows : Vector ℕ 63 :=
  Vector.ofFn (fun k => 2 ^ (1212 + k.val))

def firstLift (y : Fin 63 → ZMod 2) : Parameter :=
  fun i => ev y (firstBasisRows.get i)

def FirstRecoveryChecks (i : Fin 1275) : Prop :=
  scan (firstRecovery.get i) firstEquations.toList =
    2 ^ i.val ^^^ scan (firstBasisRows.get i) firstUnitRows.toList

def SecondChecks (i : Fin 62) : Prop :=
  radicalWord (secondPositions.get i) =
    scan (secondCorrections.get i) pivotRadicalWords.toList ∧
  secondRawEquations.get i = coefficientWord (twistedRows 1) (secondPositions.get i) ^^^
    scan (secondCorrections.get i) (pivotCoefficientWords 1).toList ∧
  secondEquations.get i = scan (secondRawEquations.get i) firstBasisRows.toList

def SecondRecoveryChecks (i : Fin 63) : Prop :=
  scan (secondRecovery.get i) secondEquations.toList =
    2 ^ i.val ^^^ (if secondFinalWord.testBit i.val then 2 ^ 58 else 0)

def FinalChecks (i : Fin 1275) : Prop :=
  dotMask 63 (firstBasisRows.get i) secondFinalWord =
    if finalParameterWord.testBit i.val then 1 else 0

def secondFinal : Fin 63 → ZMod 2 := fun i => bit secondFinalWord i.val

theorem twisted_spec (hb : BaseChecks) (t : Fin 2) :
    decodeRestrictionRows (twistedRows t) = pairingInverseᵀ * testIU t := by
  have h := congrArg (rectDecode 50) (hb.1 t)
  rw [decode_mulRows, decode_transRows] at h
  exact h.symm

def residue (p : Position) (c : ℕ) : RestrictionMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun M := M p.1 p.2 + ev (fun k => M (pivots.get k).1 (pivots.get k).2) c
  map_add' M N := by
    simp only [Matrix.add_apply, ev, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a M := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, ev,
      mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem residue_radical_zero (hb : BaseChecks) (p : Position) (c : ℕ)
    (hc : radicalWord p = scan c pivotRadicalWords.toList) (t : Fin 13) :
    residue p c (radicalKGenerator t) = 0 := by
  have he := congrArg (fun w => bit w t.val) hc
  rw [radicalWord_spec, bit_scan] at he
  simp only [hb.2.1, radicalWord_spec] at he
  change radicalKGenerator t p.1 p.2 +
    ev (fun k => radicalKGenerator t (pivots.get k).1 (pivots.get k).2) c = 0
  rw [← he, CharTwo.add_self_eq_zero]

theorem residue_span_zero (hb : BaseChecks) (p : Position) (c : ℕ)
    (hc : radicalWord p = scan c pivotRadicalWords.toList)
    (M : RestrictionMatrix) (hM : M ∈ radicalKUpperSpace) : residue p c M = 0 := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨t, rfl⟩ := hM
    exact residue_radical_zero hb p c hc t
  | zero => exact map_zero _
  | add M N _ _ hM hN => rw [map_add, hM, hN, add_zero]
  | smul a M _ hM => rw [map_smul, hM, smul_zero]

theorem actual_coefficient_spec (hb : BaseChecks) (x : Parameter)
    (t : Fin 2) (p : Position) :
    ev x (coefficientWord (twistedRows t) p) = testEffect t x p.1 p.2 := by
  rw [coefficientWord_spec, effect_twisted t x _ (twisted_spec hb t)]

theorem equation_spec (hb : BaseChecks) (x : Parameter) (t : Fin 2)
    (p : Position) (c r : ℕ)
    (hr : r = coefficientWord (twistedRows t) p ^^^
      scan c (pivotCoefficientWords t).toList) :
    ev x r = residue p c (testEffect t x) := by
  rw [hr, ev_xor, actual_coefficient_spec hb, ev_scan]
  change _ = _ + ev _ _
  simp only [hb.2.2, actual_coefficient_spec hb]
  rfl

/-- All first-test solutions, with no restriction on their 1275 coefficients. -/
theorem reconstruct_first (hb : BaseChecks) (he : ∀ i, FirstChecks i)
    (hr : ∀ i, FirstRecoveryChecks i) (x : Parameter)
    (hx : testEffect 0 x ∈ radicalKUpperSpace) :
    x = firstLift (firstFree x) := by
  have hz (i : Fin 1212) : ev x (firstEquations.get i) = 0 := by
    rw [equation_spec hb x 0 _ _ _ (he i).2]
    exact residue_span_zero hb _ _ (he i).1 _ hx
  funext i
  have hi := congrArg (ev x) (hr i)
  rw [ev_scan, ev_xor, ev_unit, ev_scan] at hi
  simp only [hz, mul_zero, Finset.sum_const_zero, firstUnitRows, get_ofFn] at hi
  have hu (k : Fin 63) : ev x (2 ^ (1212 + k.val)) = firstFree x k :=
    ev_unit x ⟨1212 + k.val, by omega⟩
  simp only [hu] at hi
  exact CharTwo.add_eq_zero.mp hi.symm

theorem restricted_spec (y : Fin 63 → ZMod 2) (r : ℕ) :
    ev y (scan r firstBasisRows.toList) = ev (firstLift y) r := by
  rw [ev_scan]
  rfl

/-- Every solution in the complete first kernel has only one scalar parameter. -/
theorem reconstruct_second (hb : BaseChecks) (he : ∀ i, SecondChecks i)
    (hr : ∀ i, SecondRecoveryChecks i) (y : Fin 63 → ZMod 2)
    (hy : testEffect 1 (firstLift y) ∈ radicalKUpperSpace) :
    y = y 58 • secondFinal := by
  have hz (i : Fin 62) : ev y (secondEquations.get i) = 0 := by
    rw [(he i).2.2, restricted_spec, equation_spec hb _ 1 _ _ _ (he i).2.1]
    exact residue_span_zero hb _ _ (he i).1 _ hy
  funext i
  have hi := congrArg (ev y) (hr i)
  rw [ev_scan, ev_xor, ev_unit] at hi
  have hu : ev y (if secondFinalWord.testBit i.val then 2 ^ 58 else 0) =
      bit secondFinalWord i.val * y 58 :=
    ev_cond_unit y (secondFinalWord.testBit i.val) (58 : Fin 63)
  rw [hu] at hi
  simp only [hz, mul_zero, Finset.sum_const_zero] at hi
  simpa only [Pi.smul_apply, secondFinal, smul_eq_mul, mul_comm] using
    CharTwo.add_eq_zero.mp hi.symm

theorem firstLift_smul (a : ZMod 2) (y : Fin 63 → ZMod 2) :
    firstLift (a • y) = a • firstLift y := by
  funext i
  exact ev_smul a y _

theorem firstLift_final (hf : ∀ i, FinalChecks i) :
    firstLift secondFinal = finalParameter := by
  funext i
  have h := congrArg (fun w => bit w 0) (hf i)
  rw [bit_dotMask] at h
  change ev (fun k : Fin 63 => bit secondFinalWord k.val) (firstBasisRows.get i) = _
  rw [h]
  cases hi : finalParameterWord.testBit i.val <;> simp [hi, bit, finalParameter]

theorem kernel_of_checks (hb : BaseChecks) (h₀ : ∀ i, FirstChecks i)
    (hr₀ : ∀ i, FirstRecoveryChecks i) (h₁ : ∀ i, SecondChecks i)
    (hr₁ : ∀ i, SecondRecoveryChecks i) (hf : ∀ i, FinalChecks i)
    (x : Parameter) (hx : ∀ t : Fin 2, testEffect t x ∈ radicalKUpperSpace) :
    ∃ a : ZMod 2, x = a • finalParameter := by
  have hfirst := reconstruct_first hb h₀ hr₀ x (hx 0)
  have hsecond := reconstruct_second hb h₁ hr₁ (firstFree x)
    (by rw [← hfirst]; exact hx 1)
  refine ⟨firstFree x 58, ?_⟩
  calc
    x = firstLift (firstFree x) := hfirst
    _ = firstLift (firstFree x 58 • secondFinal) := congrArg firstLift hsecond
    _ = firstFree x 58 • finalParameter := by rw [firstLift_smul, firstLift_final hf]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
