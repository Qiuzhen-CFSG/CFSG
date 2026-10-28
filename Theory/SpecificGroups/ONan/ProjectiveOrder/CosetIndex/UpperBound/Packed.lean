module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.Packed.Generators
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.WordModel

/-!
# Shared packed-matrix certificates for O'Nan words

`Represents.mul` and `Represents.inv` certify a directed acyclic graph of
matrix products. `WordValue.append` and `WordValue.invRev` interpret the
same nodes as signed words in `UpperBound.linearGenerators`, so repeated
subwords need only one numerical proof. `transition_of_checks` supplies
exactly the scalar equality required by the coset-cover certificate.

The reference evaluator `packedEval` is also executable and sound; for
large certificates, use stored intermediate matrices and row checks.
Every closed computation uses the ordinary kernel, with no external oracle.
Source matrices: `refs/original/onan/`; arithmetic and sample checks are in
`Packed.Arithmetic` and `Packed.Generators`.
-/

namespace ONan.OrderCertificate.UpperBound.Packed
open Subgroup.CosetWordCertificate

@[expose] public def Represents (A : Array ℕ) (g : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) : Prop :=
  decode A = g.val

public theorem Represents.mul {A B C : Array ℕ}
    {g h : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)}
    (ha : Represents A g) (hb : Represents B h) (hB : Good B)
    (hc : ∀ i, checkRow A B C i = true) : Represents C (g * h) := by
  change decode C = g.val * h.val
  rw [← mul_sound A B C hB hc, ha, hb]

public theorem good_of_check (A B C : Array ℕ)
    (h : ∀ i, checkRow A B C i = true) : Good C := by
  intro i
  have hi := h i
  simp only [checkRow, beq_iff_eq] at hi
  rw [← hi]
  simp only [entry_reduceRow]
  rfl

public theorem mul_sound_of_raw (A B C R : Array ℕ) (hB : Good B)
    (hr : ∀ i : Fin 45, rowProduct A[i.val]! B 45 = R[i.val]!)
    (hc : ∀ i : Fin 45, reduceRow R[i.val]! = C[i.val]!) :
    decode A * decode B = decode C := by
  apply mul_sound A B C hB
  intro i
  simp only [checkRow, hr i, hc i, beq_self_eq_true]

@[expose] public def packedOne : Array ℕ := encodeMatrix 1
public theorem decode_packedOne : decode packedOne = 1 := decode_encodeMatrix _
public theorem good_packedOne : Good packedOne := good_encodeMatrix _

public theorem Represents.inv {A B : Array ℕ}
    {g : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)}
    (ha : Represents A g) (hB : Good B)
    (hc : ∀ i, checkRow A B packedOne i = true) : Represents B g⁻¹ := by
  have hm : g.val * decode B = 1 := by
    rw [← ha, mul_sound A B packedOne hB hc, decode_packedOne]
  change decode B = (g⁻¹).val
  calc
    decode B = 1 * decode B := (one_mul _).symm
    _ = ((g⁻¹).val * g.val) * decode B := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    _ = (g⁻¹).val := by rw [mul_assoc, hm, mul_one]

@[expose] public def scaleRow (c a : ℕ) : ℕ := pack (fun j : Fin 45 => (c * entry a j.val) % 7)
@[expose] public def checkScaleRow (c : ℕ) (A B : Array ℕ) (i : Fin 45) : Bool :=
  scaleRow c A[i.val]! == B[i.val]!
public theorem scale_sound (c : ℕ) (A B : Array ℕ)
    (h : ∀ i, checkScaleRow c A B i = true) :
    (c : ZMod 7) • decode A = decode B := by
  ext i j
  have hi := h i
  simp only [checkScaleRow, beq_iff_eq] at hi
  change (c : ZMod 7) * (entry A[i.val]! j.val : ZMod 7) =
    (entry B[i.val]! j.val : ZMod 7)
  rw [← hi]
  simp only [entry, scaleRow]
  rw [digit_pack _ (fun _ => lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
  simp only [ZMod.natCast_mod, Nat.cast_mul]

public theorem Represents.eq_scalar {A B : Array ℕ}
    {g h : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)}
    (ha : Represents A g) (hb : Represents B h) (u : (ZMod 7)ˣ)
    (hc : ∀ i, checkScaleRow u.val.val A B i = true) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 45) u = h := by
  apply Units.ext
  have he := scale_sound u.val.val A B hc
  rw [ha, hb, ZMod.natCast_zmod_val] at he
  change g.val * Matrix.scalar (Fin 45) u.val = h.val
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  exact he

@[expose] public def WordValue (A : Array ℕ) (w : Word (Fin 4)) : Prop :=
  Represents A (eval linearGenerators w)
public theorem WordValue.append {A B C : Array ℕ} {v w : Word (Fin 4)}
    (hv : WordValue A v) (hw : WordValue B w) (hB : Good B)
    (hc : ∀ i, checkRow A B C i = true) : WordValue C (v ++ w) := by
  unfold WordValue
  rw [eval_append]
  exact hv.mul hw hB hc
public theorem WordValue.invRev {A B : Array ℕ} {w : Word (Fin 4)}
    (hw : WordValue A w) (hB : Good B)
    (hc : ∀ i, checkRow A B packedOne i = true) : WordValue B (FreeGroup.invRev w) := by
  unfold WordValue
  rw [eval_invRev]
  exact hw.inv hB hc

public theorem WordValue.nil : WordValue packedOne [] := by
  change decode packedOne = _
  rw [decode_packedOne, eval_nil]
  rfl
public theorem WordValue.letter (i : Fin 4) (s : Bool) (A : Array ℕ)
    (h : Represents A (if s then linearGenerators i else (linearGenerators i)⁻¹)) :
    WordValue A [(i,s)] := by
  unfold WordValue
  rw [eval_letter]
  exact h

/-- This is exactly the equality required by `MatrixCosetData.Valid.transition`.
The four products may be established once and reused by many transitions. -/
public theorem transition_of_checks
    (left right factor : Word (Fin 4)) (a : Fin 4)
    (L G F R LG FR : Array ℕ) (u : (ZMod 7)ˣ)
    (hl : WordValue L left) (hg : Represents G (linearGenerators a))
    (hf : WordValue F factor) (hr : WordValue R right)
    (hG : Good G) (hR : Good R)
    (hlg : ∀ i, checkRow L G LG i = true)
    (hfr : ∀ i, checkRow F R FR i = true)
    (hs : ∀ i, checkScaleRow u.val.val LG FR i = true) :
    (eval linearGenerators left * linearGenerators a) *
      Matrix.GeneralLinearGroup.scalar (Fin 45) u =
    eval linearGenerators factor * eval linearGenerators right :=
  (hl.mul hg hG hlg).eq_scalar (hf.mul hr hR hfr) u hs

/-- Reference evaluator; product certificates can instead share nodes through
`WordValue.append` and `WordValue.invRev`. -/
@[expose] public def packedEval (positive negative : Fin 4 → Array ℕ) : Word (Fin 4) → Array ℕ
  | [] => packedOne
  | (i, sign) :: w => packedMul (if sign then positive i else negative i)
      (packedEval positive negative w)

public theorem good_packedEval (positive negative : Fin 4 → Array ℕ) (w : Word (Fin 4)) :
    Good (packedEval positive negative w) := by
  cases w with
  | nil => exact good_packedOne
  | cons a w => exact good_packedMul _ _

public theorem decode_packedEval (positive negative : Fin 4 → Array ℕ)
    (hp : ∀ i, Represents (positive i) (linearGenerators i))
    (hn : ∀ i, Represents (negative i) (linearGenerators i)⁻¹)
    (w : Word (Fin 4)) : WordValue (packedEval positive negative w) w := by
  induction w with
  | nil => exact WordValue.nil
  | cons a w ih =>
    rcases a with ⟨i, sign⟩
    change decode (packedEval positive negative ((i, sign) :: w)) = _
    rw [packedEval, decode_packedMul _ _ (good_packedEval positive negative w)]
    rw [eval_cons]
    change _ = (if sign then linearGenerators i else (linearGenerators i)⁻¹).val * _
    rw [show decode (packedEval positive negative w) = (eval linearGenerators w).val from ih]
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hn i]
    · simp only [↓reduceIte]
      rw [hp i]


public theorem represents_matrixAPacked : Represents matrixAPacked linearA :=
  decode_matrixAPacked

public theorem represents_matrixBPacked : Represents matrixBPacked linearB :=
  decode_matrixBPacked

public theorem represents_matrixBInvPacked : Represents matrixBInvPacked linearB⁻¹ :=
  decode_matrixBInvPacked

public theorem wordValue_matrixAPacked : WordValue matrixAPacked [(0, true)] := by
  apply WordValue.letter
  exact represents_matrixAPacked

public theorem wordValue_matrixBPacked : WordValue matrixBPacked [(1, true)] := by
  apply WordValue.letter
  exact represents_matrixBPacked

public theorem wordValue_matrixBInvPacked : WordValue matrixBInvPacked [(1, false)] := by
  apply WordValue.letter
  exact represents_matrixBInvPacked

public theorem good_matrixBSquaredPacked : Good matrixBSquaredPacked :=
  good_of_check _ _ _ matrixB_square_check

/-- A full 45-dimensional product interpreted as a signed-word certificate. -/
public theorem wordValue_matrixBSquaredPacked :
    WordValue matrixBSquaredPacked [(1, true), (1, true)] :=
  wordValue_matrixBPacked.append wordValue_matrixBPacked good_matrixBPacked matrixB_square_check

end ONan.OrderCertificate.UpperBound.Packed
