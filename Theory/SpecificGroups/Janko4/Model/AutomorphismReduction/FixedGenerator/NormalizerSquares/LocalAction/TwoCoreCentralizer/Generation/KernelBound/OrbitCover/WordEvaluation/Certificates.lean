module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.WordEvaluation.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Relations

/-!
# Certified action on the 22 chart columns

Packed rectangular multiplication checks the bridge and each of the twelve
seed conjugates on all 22 columns. Only natural-number witnesses are supplied
by Python: the decoding lemma and every product equality are kernel checked.
The original max2 matrices act on the transported columns `h * chartMatrix`.
The parent module transports these identities back to the published column
convention. See `WordEvaluation/source/generate.py` and the attribution in
`OrbitCover/source/README.md` and `TwoCoreCentralizer/source/README.md`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.WordEvaluation
open GeneratorCertificates OrbitCoverCoordinates
open scoped Matrix
set_option maxRecDepth 10000

private def rowProduct {n : ℕ} (x : ℕ) (ys : Vector ℕ n) : ℕ :=
  xorList (List.ofFn (fun k : Fin n => if x.testBit k.val then ys.get k else 0))

private lemma rect_product {m n k : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n)
    (zs : Vector ℕ m) (h : ∀ i : Fin m, rowProduct (xs.get i) ys = zs.get i) :
    rect xs n * rect ys k = rect zs k := by
  funext i j
  rw [Matrix.mul_apply]
  change _ = bit (zs.get i) j.val
  rw [← h i, rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  simp only [rect, bit]
  cases hx : (xs.get i).testBit a.val <;> simp [hx]


set_option maxHeartbeats 1000000 in
theorem chartMatrix_apply : ∀ (i : Fin 112) (j : Fin 22),
    chartMatrix i j = basisVector j i := by
  change ∀ (i : Fin 112) (j : Fin 22),
    (if (chartRows.get i).testBit j.val then (1 : ZMod 2) else 0) =
      (if (basisColumns.get j).testBit i.val then (1 : ZMod 2) else 0)
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem bridge_chart : decodeRows hRows * chartMatrix = liftedMatrix :=
  rect_product hRows chartRows liftedRows (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem generator_lifted (i : Fin 12) :
    decodeRows (NormalClosureControl.Certificates.basisRows i.succ) * liftedMatrix =
      rect (imageRows.get i) 22 := by
  fin_cases i <;> exact rect_product _ liftedRows _ (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem lifted_coefficient (i : Fin 12) :
    liftedMatrix * coefficientAction i = rect (imageRows.get i) 22 := by
  fin_cases i <;> exact rect_product liftedRows _ _ (by decide +kernel)

theorem generator_chart (i : Fin 12) :
    decodeRows (NormalClosureControl.Certificates.basisRows i.succ) *
      (decodeRows hRows * chartMatrix) =
        decodeRows hRows * chartMatrix * coefficientAction i := by
  rw [bridge_chart, generator_lifted, lifted_coefficient]

theorem chart_synthesize (x : Fin 22 → ZMod 2) :
    chartMatrix *ᵥ x = synthesize x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, synthesize, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, chartMatrix_apply, mul_comm]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.WordEvaluation
