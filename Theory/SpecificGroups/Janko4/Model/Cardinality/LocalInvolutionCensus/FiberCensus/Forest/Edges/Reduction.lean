module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.Quotient
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.PackedData

/-!
# From packed crossing rows to literal forest conjugation edges

The kernel-row fold is proved to multiply by the actual increasing-bit source
word. An edge can be checked as `parent * actor = actor * child`, so no inverse
matrix is needed. The quotient equality is already proved in `Quotient`; equal
first rows then imply the complete group equation under the local order bound.
The lift and actor evaluations and the packed row equality are explicit inputs.

Source: ATLAS J4G1-max2W1, with provenance in `Edges/source/README.md`;
Aschbacher--Smith, refs/quasithin.pdf, printed pp.64--65, A.6.1--4 motivate
the parent local census. This conditional reduction is not the completed forest.
-/

@[expose] public section
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation Janko4.GeneratorCertificates KernelRows
attribute [local irreducible] sourceMatrix kernelProduct sourceLift actorAt

def decodeRow (x : ℕ) : Fin 112 → ZMod 2 := fun i => bit x i.val

theorem decodeRow_packedRow (x : ℕ) (ys : Vector ℕ 112) :
    decodeRow (packedRow x ys) = Matrix.vecMul (decodeRow x) (decodeRows ys) := by
  funext j
  rw [decodeRow, packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin 112, bit (if x.testBit k.val then ys.get k else 0) j.val) =
    ∑ k : Fin 112, bit x k.val * bit (ys.get k) j.val
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases x.testBit k.val <;> simp

/-- Right multiplication by the thirteen actual factors, in increasing bit order. -/
def kernelRow (x : ℕ) (m : Fin 8192) : ℕ :=
  (List.ofFn (fun i : Fin 13 => i)).foldl
    (fun r i => if m.val.testBit i.val then packedRow r (factorRows i) else r) x

private theorem kernelRow_fold (m : Fin 8192) (l : List (Fin 13)) (x : ℕ) :
    decodeRow (l.foldl (fun r i =>
      if m.val.testBit i.val then packedRow r (factorRows i) else r) x) =
    Matrix.vecMul (decodeRow x)
      ((l.map (fun i => if m.val.testBit i.val then decodeRows (factorRows i) else 1)).prod) := by
  induction l generalizing x with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    cases hb : m.val.testBit i.val
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      exact ih x
    · simp only [↓reduceIte]
      rw [ih, decodeRow_packedRow, Matrix.vecMul_vecMul]

theorem kernelRow_spec (x : ℕ) (m : Fin 8192) :
    decodeRow (kernelRow x m) = Matrix.vecMul (decodeRow x) (sourceMatrix (kernelProduct m)) := by
  rw [kernelRow, kernelRow_fold, eval_kernelProduct]
  simp only [matrixProduct, binaryProduct, List.map_ofFn]
  rfl

theorem firstRow_mul (a b : sourceSubgroup) :
    firstRow (a * b) = Matrix.vecMul (firstRow a) (sourceMatrix b) := by
  unfold firstRow
  rw [map_mul, Matrix.mul_apply_eq_vecMul]

/-- The integer equation whose two sides decode to the crossing-product rows. -/
noncomputable def PackedEdge (k : Fin 11) (n : ℕ) : Prop :=
  packedRow (packedRow (KernelSeparation.row (maskAt k (parentAt k n)).val)
      (liftRows (fiberIndex k))) (actorRowsAt k n) =
    packedRow (kernelRow ((actorRowsAt k n).get 0) (maskAt k n)) (liftRows (fiberIndex k))

theorem crossRow_of_packed (k : Fin 11) (n : ℕ)
    (hl : sourceMatrix (sourceLift (fiberIndex k)) = decodeRows (liftRows (fiberIndex k)))
    (ha : sourceMatrix (actorAt k n) = decodeRows (actorRowsAt k n))
    (he : PackedEdge k n) :
    firstRow (sourceElement (fiberIndex k) (maskAt k (parentAt k n)) * actorAt k n) =
      firstRow (actorAt k n * sourceElement (fiberIndex k) (maskAt k n)) := by
  have hkernel (m : Fin 8192) : firstRow (kernelProduct m) = decodeRow (KernelSeparation.row m.val) := by
    funext j
    exact firstRow_kernelProduct m j
  have hactor : firstRow (actorAt k n) = decodeRow ((actorRowsAt k n).get 0) := by
    change sourceMatrix (actorAt k n) 0 = _
    rw [ha]
    rfl
  have h := congrArg decodeRow he
  simp only [decodeRow_packedRow, kernelRow_spec] at h
  simpa only [sourceElement, ← mul_assoc, firstRow_mul, hkernel, hactor, hl, ha] using h

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges

namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
open Coordinates Edges KernelRows
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound
attribute [local irreducible] sourceLift actorAt kernelProduct firstRow sourceMatrix sourceElement

/-- Crossing products require no inverse-matrix certificate. Their quotient
images agree by the now-certified actor centralization. -/
theorem edge_of_crossRow (hH : Nat.card H ≤ 21799895040)
    (k : Fin 11) (n : Fin (fiberBound k))
    (hr : firstRow (sourceElement (fiberIndex k) (maskAt k (parentAt k n.val)) * actorAt k n.val) =
      firstRow (actorAt k n.val * sourceElement (fiberIndex k) (maskAt k n.val))) :
    Edge k n.val := by
  have hq : quotientMap (sourceElement (fiberIndex k) (maskAt k (parentAt k n.val)) * actorAt k n.val) =
      quotientMap (actorAt k n.val * sourceElement (fiberIndex k) (maskAt k n.val)) := by
    simp only [map_mul, quotientMap_sourceElement]
    exact (quotient_commute_actorAt k n).eq
  have he := eq_of_quotient_eq_of_firstRow hH _ _ hq hr
  unfold Edge
  rw [mul_assoc, he, inv_mul_cancel_left]

/-- Final edge reduction to independently checkable matrix evaluations and rows. -/
theorem edge_of_packed (hH : Nat.card H ≤ 21799895040)
    (k : Fin 11) (n : Fin (fiberBound k))
    (hl : sourceMatrix (sourceLift (fiberIndex k)) = decodeRows (liftRows (fiberIndex k)))
    (ha : sourceMatrix (actorAt k n.val) = decodeRows (actorRowsAt k n.val))
    (he : PackedEdge k n.val) : Edge k n.val :=
  edge_of_crossRow hH k n (crossRow_of_packed k n.val hl ha he)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest
