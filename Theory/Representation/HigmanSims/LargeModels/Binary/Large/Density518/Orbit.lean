module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Setup

/-!
# Shared-prefix induction for the literal degree-518 orbit words

A strictly earlier parent lets each orbit vector be verified once. Column
words prepend a generator, while row words append one; the induction lemmas
connect precisely these operations to the word matrices in `Setup.lean`.
The unit pairing and initial row are also kernel-checked here. Local numerical
transitions and basis inverse identities remain the certificate producers'
obligations. Source: ATLAS HSG1-f2r518B0 and `Binary/source/density518.json`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518
open Matrix

theorem column_orbit_of_prefix_steps
    (parent : Fin 517 → Fin 518) (letter : Fin 517 → Bool)
    (hparent : ∀ i, parent i < i.succ)
    (hroot : columnWords[0]! = []) (hstart : C.col 0 = u)
    (hword : ∀ i, columnWords[i.succ.val]! = letter i :: columnWords[(parent i).val]!)
    (hstep : ∀ i, (if letter i then B else A).mulVec (C.col (parent i)) = C.col i.succ) :
    ∀ i, (columnActor i).mulVec u = C.col i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero =>
      change (word columnWords[0]!).mulVec u = C.col 0
      rw [hroot, word, one_mulVec, hstart]
    | succ i =>
      change (word columnWords[i.succ.val]!).mulVec u = C.col i.succ
      rw [hword, word, ← mulVec_mulVec]
      change (if letter i then B else A).mulVec ((columnActor (parent i)).mulVec u) = _
      rw [ih (parent i) (hparent i)]
      exact hstep i

theorem row_orbit_of_prefix_steps
    (parent : Fin 517 → Fin 518) (letter : Fin 517 → Bool)
    (hparent : ∀ i, parent i < i.succ)
    (hroot : rowWords[0]! = []) (hstart : R.row 0 = v)
    (hword : ∀ i, rowWords[i.succ.val]! = rowWords[(parent i).val]! ++ [letter i])
    (hstep : ∀ i, vecMul (R.row (parent i)) (if letter i then B else A) = R.row i.succ) :
    ∀ i, vecMul v (rowActor i) = R.row i := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero =>
      change vecMul v (word rowWords[0]!) = R.row 0
      rw [hroot, word, vecMul_one, hstart]
    | succ i =>
      change vecMul v (word rowWords[i.succ.val]!) = R.row i.succ
      rw [hword, word_append, word, word, mul_one, ← vecMul_vecMul]
      change vecMul (vecMul v (rowActor (parent i))) (if letter i then B else A) = _
      rw [ih (parent i) (hparent i)]
      exact hstep i

theorem pair_eq_one : dotProduct v u = 1 := by decide +kernel

theorem row_start : R.row 0 = v :=
  congrArg (RowArithmetic.vector 518)
    (by decide +kernel : rowRows[0]! = functionalRow)

theorem column_word_root : columnWords[0]! = [] := by decide +kernel
theorem row_word_root : rowWords[0]! = [] := by decide +kernel

/-- Column transitions and a basis inverse discharge the density span premise. -/
theorem column_span_of_prefix_certificates
    (parent : Fin 517 → Fin 518) (letter : Fin 517 → Bool)
    (hparent : ∀ i, parent i < i.succ) (hstart : C.col 0 = u)
    (hword : ∀ i, columnWords[i.succ.val]! = letter i :: columnWords[(parent i).val]!)
    (hstep : ∀ i, (if letter i then B else A).mulVec (C.col (parent i)) = C.col i.succ)
    (hinv : C * Ci = 1) :
    Submodule.span (ZMod 2) (Set.range (fun i => (columnActor i).mulVec u)) = ⊤ :=
  column_span_of_certificates (column_orbit_of_prefix_steps parent letter hparent
    column_word_root hstart hword hstep) hinv

/-- Row transitions and a basis inverse discharge the density span premise. -/
theorem row_span_of_prefix_certificates
    (parent : Fin 517 → Fin 518) (letter : Fin 517 → Bool)
    (hparent : ∀ i, parent i < i.succ)
    (hword : ∀ i, rowWords[i.succ.val]! = rowWords[(parent i).val]! ++ [letter i])
    (hstep : ∀ i, vecMul (R.row (parent i)) (if letter i then B else A) = R.row i.succ)
    (hinv : R * Ri = 1) :
    Submodule.span (ZMod 2) (Set.range (fun i => vecMul v (rowActor i))) = ⊤ :=
  row_span_of_certificates (row_orbit_of_prefix_steps parent letter hparent
    row_word_root row_start hword hstep) hinv

end Representation.HigmanSims.LargeModels.Binary.Large.Density518
