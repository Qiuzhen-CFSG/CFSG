module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.ModularFaithfulness.Data

/-!
# Checked modular vector certificates

Sparse formulas are proved for multiplication by the literal reduced generators.
The image tables then certify invariance of the finite row set. A membership
bit mask certifies three distinguishing translation tests and the marked rows.
All finite decisions below use the Lean kernel; no native evaluation is trusted.
The numerical source and reproducible data are recorded in `Data`.
-/

-- The unchunked 378-point check peaked at 7.0 GiB. Keep the finite
-- certificates in 63-point blocks and check these declarations sequentially.
set_option Elab.async false

public section
open Atlas.Algebra Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.ModularFaithfulness

private theorem reducedA : matrixA.map reductionScalars =
    (!![1,0,0,0,0,0; 0,0,1,0,0,0; 0,1,0,0,0,0;
        0,0,0,0,1,0; 0,0,0,1,0,0; 0,0,0,0,0,1] : Matrix _ _ GoldenFour) := by
  decide +kernel

private theorem reducedB : matrixB.map reductionScalars =
    let z := goldenFourTau + 1
    (!![0,1,0,0,0,0; 0,1,0,0,1,z; 0,0,1,0,0,0;
        0,0,z,0,0,1; 1,1,0,z,0,0; 0,0,0,1,0,0] : Matrix _ _ GoldenFour) := by
  decide +kernel

private theorem row_mul_A (v : Row) : v ᵥ* matrixA.map reductionScalars = actA v := by
  rw [reducedA]
  funext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_succ, actA]

private theorem row_mul_B (v : Row) : v ᵥ* matrixB.map reductionScalars = actB v := by
  rw [reducedB]
  funext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_succ, actB, add_assoc]

/-- Assemble six small checks without reducing one long finite quantifier. -/
private theorem of_blocks (P : Fin 378 → Prop)
    (h : ∀ b : Fin 6, ∀ i : Fin 63, P (Fin.ofNat 378 (63 * b.val + i.val)))
    (j : Fin 378) : P j := by
  have hb : j.val / 63 < 6 := by omega
  have hi : j.val % 63 < 63 := Nat.mod_lt _ (by decide)
  have he : Fin.ofNat 378 (63 * (j.val / 63) + j.val % 63) = j := by
    apply Fin.ext
    simp only [Fin.val_ofNat]
    omega
  simpa only [he] using h ⟨j.val / 63, hb⟩ ⟨j.val % 63, hi⟩

private theorem checkA0 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (0 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem checkA1 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (63 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem checkA2 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (126 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem checkA3 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (189 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem checkA4 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (252 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem checkA5 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (315 + k.val)
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by decide +kernel

private theorem point_actA (i : Fin 378) :
    actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!)) := by
  apply of_blocks (fun i => actA (point i) = point (Fin.ofNat 378 (imageA[i.val]!))) ?_ i
  intro b
  fin_cases b
  · exact checkA0
  · exact checkA1
  · exact checkA2
  · exact checkA3
  · exact checkA4
  · exact checkA5

private theorem checkB0 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (0 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem checkB1 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (63 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem checkB2 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (126 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem checkB3 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (189 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem checkB4 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (252 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem checkB5 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (315 + k.val)
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by decide +kernel

private theorem point_actB (i : Fin 378) :
    actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!)) := by
  apply of_blocks (fun i => actB (point i) = point (Fin.ofNat 378 (imageB[i.val]!))) ?_ i
  intro b
  fin_cases b
  · exact checkB0
  · exact checkB1
  · exact checkB2
  · exact checkB3
  · exact checkB4
  · exact checkB5

theorem stepA (i : Fin 378) : point i ᵥ* matrixA.map reductionScalars =
    point (Fin.ofNat 378 (imageA[i.val]!)) := by
  rw [row_mul_A]
  exact point_actA i

theorem stepB (i : Fin 378) : point i ᵥ* matrixB.map reductionScalars =
    point (Fin.ofNat 378 (imageB[i.val]!)) := by
  rw [row_mul_B]
  exact point_actB i

private theorem admissible0 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (0 + k.val)
    admissible (point i) := by decide +kernel

private theorem admissible1 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (63 + k.val)
    admissible (point i) := by decide +kernel

private theorem admissible2 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (126 + k.val)
    admissible (point i) := by decide +kernel

private theorem admissible3 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (189 + k.val)
    admissible (point i) := by decide +kernel

private theorem admissible4 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (252 + k.val)
    admissible (point i) := by decide +kernel

private theorem admissible5 : ∀ k : Fin 63,
    let i := Fin.ofNat 378 (315 + k.val)
    admissible (point i) := by decide +kernel

theorem point_admissible (i : Fin 378) : admissible (point i) := by
  apply of_blocks (fun i => admissible (point i)) ?_ i
  intro b
  fin_cases b
  · exact admissible0
  · exact admissible1
  · exact admissible2
  · exact admissible3
  · exact admissible4
  · exact admissible5

private theorem distinguish0_0 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (0 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0_1 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (63 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0_2 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (126 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0_3 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (189 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0_4 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (252 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0_5 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (315 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 0 l)) → point j = seed 0 := by
  decide +kernel

private theorem distinguish0 (j : Fin 378) :
    (∀ k : Fin 3, admissible (point j + shift 0 k)) → point j = seed 0 := by
  apply of_blocks (fun j => (∀ k : Fin 3, admissible (point j + shift 0 k)) →
    point j = seed 0) ?_ j
  intro b
  fin_cases b
  · exact distinguish0_0
  · exact distinguish0_1
  · exact distinguish0_2
  · exact distinguish0_3
  · exact distinguish0_4
  · exact distinguish0_5

private theorem distinguish1_0 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (0 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1_1 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (63 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1_2 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (126 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1_3 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (189 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1_4 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (252 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1_5 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (315 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 1 l)) → point j = seed 1 := by
  decide +kernel

private theorem distinguish1 (j : Fin 378) :
    (∀ k : Fin 3, admissible (point j + shift 1 k)) → point j = seed 1 := by
  apply of_blocks (fun j => (∀ k : Fin 3, admissible (point j + shift 1 k)) →
    point j = seed 1) ?_ j
  intro b
  fin_cases b
  · exact distinguish1_0
  · exact distinguish1_1
  · exact distinguish1_2
  · exact distinguish1_3
  · exact distinguish1_4
  · exact distinguish1_5

private theorem distinguish2_0 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (0 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2_1 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (63 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2_2 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (126 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2_3 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (189 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2_4 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (252 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2_5 : ∀ k : Fin 63,
    let j := Fin.ofNat 378 (315 + k.val)
    (∀ l : Fin 3, admissible (point j + shift 2 l)) → point j = seed 2 := by
  decide +kernel

private theorem distinguish2 (j : Fin 378) :
    (∀ k : Fin 3, admissible (point j + shift 2 k)) → point j = seed 2 := by
  apply of_blocks (fun j => (∀ k : Fin 3, admissible (point j + shift 2 k)) →
    point j = seed 2) ?_ j
  intro b
  fin_cases b
  · exact distinguish2_0
  · exact distinguish2_1
  · exact distinguish2_2
  · exact distinguish2_3
  · exact distinguish2_4
  · exact distinguish2_5

/-- Three translates distinguish each seed among all indexed vectors. -/
theorem distinguish (i : Fin 3) (j : Fin 378)
    (h : ∀ k : Fin 3, admissible (point j + shift i k)) : point j = seed i := by
  fin_cases i
  · exact distinguish0 j h
  · exact distinguish1 j h
  · exact distinguish2 j h

theorem seed_eq : ∀ i : Fin 3, point (seedIndex i) = seed i := by decide +kernel

theorem shift_eq : ∀ i k : Fin 3, point (shiftIndex i k) = seed i + shift i k := by
  decide +kernel

theorem coefficients_eq : ∀ i k : Fin 3,
    shift i k = coefficients i k ᵥ* modularRows := by decide +kernel

theorem frame_inverse : frameInverse * frame = 1 := by decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.ModularFaithfulness
