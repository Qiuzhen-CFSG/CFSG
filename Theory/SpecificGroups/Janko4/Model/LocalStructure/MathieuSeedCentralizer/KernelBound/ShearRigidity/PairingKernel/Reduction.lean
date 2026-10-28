module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingKernel.Data

/-!
# Arbitrary-coefficient reconstruction of the pairing kernel

Packed symmetry equations are evaluated as linear forms. The recovery
identities reconstruct every coefficient from entries 610 and 612; the
corresponding matrix combinations are the identity and `extraShear`.
The numerical hypotheses here are discharged in the checked modules, and
`PairingKernel.lean` exports the resulting unconditional theorem.

Source: `source/README.md` and the reproduced `kernel-linear.json`.
-/

@[expose] public section
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership FiniteAlgebra

attribute [local irreducible] twistedRows pairedWords positions equations recovery kernelWords
  survivorMixedWords mixedWords

abbrev Coefficients := Fin 616 → ZMod 2

def candidateSum : Coefficients →ₗ[ZMod 2] HalfMatrix :=
  Fintype.linearCombination (ZMod 2) candidateBasis

def kernelVector (t : Fin 2) : Coefficients := fun k => bit (kernelWords.get t) k.val

def TwistedChecks : Prop := ∀ i : Fin 56,
  scan (wallPairingRows.get i) r0InverseRows.toList = twistedRows.get i

def ProductChecks (k : Fin 616) : Prop := ∀ i : Fin 56,
  scan (twistedRows.get i) (slices 56 56 (mixedWords.get k)).toList =
    (slices 56 56 (pairedWords.get k)).get i

def EquationChecks (e : Fin 614) : Prop := ∀ k : Fin 616,
  (equations.get e).testBit k.val =
    ((pairedWords.get k).testBit (56 * (positions.get e).1.val + (positions.get e).2.val) !=
     (pairedWords.get k).testBit (56 * (positions.get e).2.val + (positions.get e).1.val))

def RecoveryChecks (k : Fin 616) : Prop :=
  scan (recovery.get k) equations.toList =
    2 ^ k.val ^^^ (if (kernelWords.get 0).testBit k.val then 2 ^ 610 else 0) ^^^
      (if (kernelWords.get 1).testBit k.val then 2 ^ 612 else 0)

def SurvivorChecks (t : Fin 2) : Prop :=
  scan (kernelWords.get t) mixedWords.toList = survivorMixedWords.get t ∧
  ∀ i : Fin 56,
    scan (r0InverseRows.get i) (slices 56 56 (survivorMixedWords.get t)).toList =
      if t = 0 then 2 ^ i.val else extraShearRows.get i

private lemma half_slices (w : ℕ) : rectDecode 56 (slices 56 56 w) = decodeHalf w := by
  ext i j
  simp only [rectDecode, slices, get_ofFn, decodeHalf, bit]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]

private lemma decode_scan (c : ℕ) :
    decodeHalf (scan c mixedWords.toList) =
      ∑ k : Fin 616, bit c k.val • mixedBasis k := by
  ext i j
  simp only [decodeHalf, bit_scan, ev, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mixedBasis]

private lemma mul_of_scan {m n p : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m)
    (h : ∀ i, scan (xs.get i) ys.toList = zs.get i) :
    rectDecode n xs * rectDecode p ys = rectDecode p zs := by
  rw [← decode_mulRows]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = zs.get ⟨i, hi⟩
  rw [get_ofFn]
  exact h ⟨i, hi⟩

theorem twisted_spec (ht : TwistedChecks) :
    rectDecode 56 twistedRows = wallPairing * inverseRestriction :=
  (mul_of_scan _ _ _ ht).symm

theorem paired_spec (ht : TwistedChecks) (hp : ∀ k, ProductChecks k) (k : Fin 616) :
    decodeHalf (pairedWords.get k) = wallPairing * candidateBasis k := by
  calc
    _ = rectDecode 56 twistedRows * rectDecode 56 (slices 56 56 (mixedWords.get k)) :=
      (half_slices _).symm.trans (mul_of_scan _ _ _ (hp k)).symm
    _ = _ := by
      rw [twisted_spec ht, half_slices]
      rw [candidateBasis, mixedBasis, mul_assoc]

theorem equation_spec (ht : TwistedChecks) (hp : ∀ k, ProductChecks k)
    (he : ∀ e, EquationChecks e) (x : Coefficients) (e : Fin 614) :
    ev x (equations.get e) =
      (wallPairing * candidateSum x) (positions.get e).1 (positions.get e).2 +
      (wallPairing * candidateSum x) (positions.get e).2 (positions.get e).1 := by
  have hb (k : Fin 616) : bit (equations.get e) k.val =
      (wallPairing * candidateBasis k) (positions.get e).1 (positions.get e).2 +
      (wallPairing * candidateBasis k) (positions.get e).2 (positions.get e).1 := by
    rw [← paired_spec ht hp]
    simp only [decodeHalf, bit, he e k]
    cases (pairedWords.get k).testBit (56 * (positions.get e).1.val + (positions.get e).2.val) <;>
      cases (pairedWords.get k).testBit (56 * (positions.get e).2.val + (positions.get e).1.val) <;>
      decide
  simp only [candidateSum, Fintype.linearCombination_apply, Matrix.mul_sum,
    Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ev, hb,
    mul_comm]
  simp only [mul_add, Finset.sum_add_distrib]

private lemma ev_cond_unit (x : Coefficients) (b : Bool) (i : ℕ) (hi : i < 616) :
    ev x (if b then 2 ^ i else 0) = (if b then 1 else 0) * x ⟨i, hi⟩ := by
  cases b
  · simp [ev_zero]
  · simpa only [Bool.true_eq, ↓reduceIte, one_mul] using ev_unit x ⟨i, hi⟩

/-- Reconstruction covers every coefficient vector satisfying the symmetry equations. -/
theorem reconstruct_coefficients (hr : ∀ k, RecoveryChecks k) (x : Coefficients)
    (hx : ∀ e, ev x (equations.get e) = 0) :
    x = x 610 • kernelVector 0 + x 612 • kernelVector 1 := by
  funext k
  have h := congrArg (ev x) (hr k)
  have hu0 : ev x (if (kernelWords.get 0).testBit k.val then 2 ^ 610 else 0) =
      (if (kernelWords.get 0).testBit k.val then 1 else 0) * x 610 :=
    ev_cond_unit x ((kernelWords.get 0).testBit k.val) 610 (by decide)
  have hu1 : ev x (if (kernelWords.get 1).testBit k.val then 2 ^ 612 else 0) =
      (if (kernelWords.get 1).testBit k.val then 1 else 0) * x 612 :=
    ev_cond_unit x ((kernelWords.get 1).testBit k.val) 612 (by decide)
  rw [ev_scan, ev_xor, ev_xor, ev_unit, hu0, hu1] at h
  simp only [hx, mul_zero, Finset.sum_const_zero] at h
  change x k = x 610 * bit (kernelWords.get 0) k.val +
    x 612 * bit (kernelWords.get 1) k.val
  have hz : x k + ((if (kernelWords.get 0).testBit k.val then 1 else 0) * x 610 +
      (if (kernelWords.get 1).testBit k.val then 1 else 0) * x 612) = 0 := by
    simpa only [add_assoc] using h.symm
  simpa only [bit, mul_comm] using CharTwo.add_eq_zero.mp hz

theorem survivor_spec (hs : ∀ t, SurvivorChecks t) (t : Fin 2) :
    candidateSum (kernelVector t) = if t = 0 then 1 else extraShear := by
  have hsum : candidateSum (kernelVector t) =
      inverseRestriction * decodeHalf (survivorMixedWords.get t) := by
    rw [← (hs t).1, decode_scan, Matrix.mul_sum]
    simp only [candidateSum, Fintype.linearCombination_apply, kernelVector,
      candidateBasis, Matrix.mul_smul]
  rw [hsum, ← half_slices]
  let resultRows : Vector ℕ 56 :=
    Vector.ofFn (fun i => if t = 0 then 2 ^ i.val else extraShearRows.get i)
  have hmul : inverseRestriction * rectDecode 56 (slices 56 56 (survivorMixedWords.get t)) =
      rectDecode 56 resultRows := mul_of_scan _ _ _ (by simpa only [resultRows, get_ofFn] using (hs t).2)
  rw [hmul]
  split_ifs with ht
  · simpa only [resultRows, ht, if_true] using rectDecode_one 56
  · ext i j
    simp only [rectDecode, resultRows, get_ofFn, ht, if_false, extraShear, rowsHalf]

/-- The concrete arithmetic identities imply the exact requested matrix statement. -/
theorem pairing_kernel_of_checks (ht : TwistedChecks) (hp : ∀ k, ProductChecks k)
    (he : ∀ e, EquationChecks e) (hr : ∀ k, RecoveryChecks k)
    (hs : ∀ t, SurvivorChecks t) (H : HalfMatrix) (hH : H ∈ candidateSpan)
    (hsym : (wallPairing * H)ᵀ = wallPairing * H) :
    ∃ a b : ZMod 2, H = a • (1 : HalfMatrix) + b • extraShear := by
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hH
  change candidateSum x = H at hx
  have hz (e : Fin 614) : ev x (equations.get e) = 0 := by
    rw [equation_spec ht hp he, hx]
    have h := congrFun (congrFun hsym (positions.get e).1) (positions.get e).2
    change (wallPairing * H) (positions.get e).2 (positions.get e).1 =
      (wallPairing * H) (positions.get e).1 (positions.get e).2 at h
    rw [h, CharTwo.add_self_eq_zero]
  refine ⟨x 610, x 612, ?_⟩
  calc
    H = candidateSum x := hx.symm
    _ = candidateSum (x 610 • kernelVector 0 + x 612 • kernelVector 1) :=
      congrArg candidateSum (reconstruct_coefficients hr x hz)
    _ = _ := by
      rw [map_add, map_smul, map_smul, survivor_spec hs, survivor_spec hs]
      rfl

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.PairingCertificate
