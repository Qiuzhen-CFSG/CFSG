module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.ContractionChecks.Wide
/-!
# Sequential tensor certificates

List traversal computes each outer product and selected XOR once, avoiding
repeated finite-index lookup during kernel reduction. The checked raw entries
need cover only the support of the tested functionals. `contract_of_raw` proves
that this support condition suffices for the exact natural-number contraction,
and `outputsAt_spec` connects the numerical checks to `ContractionCheck`.

Source conventions and ATLAS attribution: `../../../../source/README.md`
and `../source/README.md`. No source-column or image calibration is assumed.
-/

@[expose] public section
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable.ContractionChecks

def tensorZip (xs ys : Vector ℕ 50) : ℕ :=
  xorList (List.zipWith (fun x y => spreadWide x * (y % 2^125)) xs.toList ys.toList)

theorem tensorZip_eq (xs ys : Vector ℕ 50) : tensorFast xs ys = tensorZip xs ys := by
  rw [tensorWide_eq]
  unfold tensorWide tensorZip
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_zipWith]
    rfl

def all₂ {α β : Type} {n : ℕ} (f : α → β → Bool) (xs : Vector α n)
    (ys : Vector β n) : Bool := (List.zipWith f xs.toList ys.toList).all id

theorem all₂_spec {α β : Type} {n : ℕ} (f : α → β → Bool)
    (xs : Vector α n) (ys : Vector β n) (h : all₂ f xs ys = true) (i : Fin n) :
    f (xs.get i) (ys.get i) = true := by
  have hi : i.val < (List.zipWith f xs.toList ys.toList).length := by simp [i.isLt]
  have hh := List.all_eq_true.mp h _ (List.getElem_mem hi)
  change f xs[i.val] ys[i.val] = true
  simpa only [List.getElem_zipWith, Vector.getElem_toList, id_eq] using hh

def selected (w u v : ℕ) : Bool :=
  ((w >>> (u*50-u*(u+1)/2)) <<< (u+1)).testBit v

def checkRawRow (w u : ℕ) (c : Vector ℕ 50) (D : ColumnCoefficients)
    (rev : Bool) (rs : Vector ℕ 50) : Bool :=
  all₂ (fun dv r => if selected w u dv.2 then
      (if rev then tensorZip dv.1 c else tensorZip c dv.1) == r else true)
    D.zipIdx rs

def checkRaw (w : ℕ) (C D : ColumnCoefficients) (rev : Bool)
    (rs : ColumnCoefficients) : Bool :=
  all₂ (fun cu r => checkRawRow w cu.2 cu.1 D rev r) C.zipIdx rs

theorem checkRaw_spec (w : ℕ) (C D : ColumnCoefficients) (rev : Bool)
    (rs : ColumnCoefficients) (h : checkRaw w C D rev rs = true)
    (u v : Fin 50) (hs : selected w u.val v.val = true) :
    (if rev then tensorFast (D.get v) (C.get u) else tensorFast (C.get u) (D.get v)) =
      (rs.get u).get v := by
  have hu := all₂_spec _ _ _ h u
  have hv := all₂_spec _ _ _ hu v
  have hg {α : Type} (xs : Vector α 50) (i : Fin 50) :
      xs.zipIdx.get i = (xs.get i, i.val) := by
    change xs.zipIdx[i.val] = (xs[i.val], i.val)
    simp
  simp only [hg] at hv
  simp only [hs, if_true, beq_iff_eq, ← tensorZip_eq] at hv
  exact hv

theorem selected_lt {w : ℕ} {u v : Fin 50} (h : selected w u.val v.val = true) : u < v := by
  simp only [selected, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem selected_mono (w m : ℕ) (hm : w &&& m = w) (u v : Fin 50)
    (h : selected w u.val v.val = true) : selected m u.val v.val = true := by
  simp only [selected, Nat.testBit_shiftLeft, Nat.testBit_shiftRight] at h ⊢
  have ht := congrArg (fun x : ℕ => x.testBit (u.val*50-u.val*(u.val+1)/2+(v.val-(u.val+1)))) hm
  simp only [Nat.testBit_and] at ht
  simp only [Bool.and_eq_true] at h ⊢
  have hh := ht.trans h.2
  simp only [Bool.and_eq_true] at hh
  exact ⟨h.1, hh.2⟩

theorem contract_of_raw (w m : ℕ) (C D : ColumnCoefficients) (rev : Bool)
    (rs : ColumnCoefficients) (hr : checkRaw m C D rev rs = true) (hm : w &&& m = w) :
    contract w (rawBlockFast C D rev) = contract w rs := by
  unfold contract
  apply congrArg xorList
  apply congrArg List.ofFn
  funext u
  unfold rowProduct
  apply congrArg xorList
  apply congrArg List.ofFn
  funext v
  by_cases h : selected w u.val v.val = true
  · have hs : (weightRow w u).testBit v.val = true := h
    simp only [hs, if_true, rawBlockFast, get_ofFn, selected_lt h]
    exact checkRaw_spec m C D rev rs hr u v (selected_mono w m hm u v h)
  · have hs : (weightRow w u).testBit v.val = false := Bool.eq_false_iff.mpr h
    simp only [hs, Bool.false_eq_true, if_false]

def contractZip (w : ℕ) (rs : ColumnCoefficients) : ℕ :=
  xorList (rs.toList.zipIdx.map (fun ru =>
    xorList (ru.1.toList.zipIdx.map (fun xv => if selected w ru.2 xv.2 then xv.1 else 0))))

theorem contractZip_eq (w : ℕ) (rs : ColumnCoefficients) : contract w rs = contractZip w rs := by
  unfold contract contractZip
  apply congrArg xorList
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_zipIdx]
    simp only [Vector.getElem_toList, Nat.zero_add]
    unfold rowProduct
    apply congrArg xorList
    apply List.ext_getElem
    · simp
    · intro j hi hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_zipIdx,
        Vector.getElem_toList, Nat.zero_add]
      rfl

/-- Bounded lookup avoids constructing a large zipped vector in the kernel. -/
def checkOutputAt (t : Fin 10) (mask : ℕ) (rs rt : ColumnCoefficients) (e : ℕ) : Bool :=
  if h : e < 987 then
    let i : Fin 987 := ⟨e, h⟩
    let test := tests.get i
    if test.1 == t then
      ((test.2 &&& mask) == test.2) &&
      (contractZip test.2 rs == ordered.get i) &&
      (contractZip test.2 rt == reversed.get i)
    else true
  else true

theorem outputsAt_spec (t : Fin 10) (mask : ℕ) (rs rt : ColumnCoefficients)
    (hr : checkRaw mask columns (images.get t) false rs = true)
    (ht : checkRaw mask columns (images.get t) true rt = true)
    (e : Fin 987) (ho : checkOutputAt t mask rs rt e.val = true)
    (he : (tests.get e).1 = t) : ContractionCheck e := by
  simp only [checkOutputAt, dif_pos e.isLt, he, beq_self_eq_true, if_true,
    Bool.and_eq_true, beq_iff_eq] at ho
  unfold ContractionCheck
  rw [he, contract_of_raw _ mask _ _ _ rs hr ho.1.1,
    contract_of_raw _ mask _ _ _ rt ht ho.1.1, contractZip_eq, contractZip_eq]
  exact ⟨ho.1.2, ho.2⟩

/-- Twenty blocks of fifty indices cover all 987 published tests. -/
theorem batches_cover (f : ℕ → Bool)
    (h : ∀ b : Fin 20, (List.range' (50*b.val) 50).all f = true)
    (e : Fin 987) : f e.val = true := by
  have hb : e.val / 50 < 20 := by omega
  exact List.all_eq_true.mp (h ⟨e.val / 50, hb⟩) e.val
    (List.mem_range'_1.mpr (by dsimp; omega))

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable.ContractionChecks
