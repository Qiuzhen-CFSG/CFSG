module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.Marking

/-!
# Explicit binary coordinates for the Hermitian nine-space

Write each GF(4) coefficient as `re + im * a`, with `a² = a + 1` in the
computable field `PairPlaneCoordinates.Four`. The coordinate order is the
three diagonal coefficients followed by the real and imaginary coefficients
of entries `(0,1)`, `(0,2)` and `(1,2)`. The Hermitian condition forces the
imaginary diagonal coefficients to vanish and determines the lower entries.

`binaryMatrix` computes each column by encoding a binary unit vector, applying
`X ↦ A X σ(A)ᵀ` over `Four` (where `σ(x) = x²`), and decoding. Its definition
uses neither a chosen basis nor the noncomputable field equivalence. Transport
through the existing `fieldEquiv` proves `binaryCoordinates_action`, which
supplies the coordinate premise of the native correction-block consumer.

Source: Aschbacher–Smith, H.4.2 setup and H.4.4, printed pp.380–381;
Guralnick–Malle I, Proposition 5.1, pp.15–16. The latter's small-module
application is also discussed in Aschbacher–Smith, printed pp.451–452,457.
-/

open Representation Sporadic.Mathieu
open M23Geometry.PairPlaneCoordinates
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule

namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.HermitianCoordinates

public abbrev Mat := Matrix (Fin 3) (Fin 3) Four
public abbrev Vec := Fin 9 → ZMod 2

/-- The Hermitian matrix with the prescribed nine binary coordinates. -/
@[expose] public def encode (c : Vec) : Mat :=
  !![⟨c 0, 0⟩, ⟨c 3, c 4⟩, ⟨c 5, c 6⟩;
     (⟨c 3, c 4⟩ : Four) ^ 2, ⟨c 1, 0⟩, ⟨c 7, c 8⟩;
     (⟨c 5, c 6⟩ : Four) ^ 2, (⟨c 7, c 8⟩ : Four) ^ 2, ⟨c 2, 0⟩]

/-- Diagonal real parts, then the real/imaginary parts of the three upper entries. -/
@[expose] public def decode (X : Mat) : Vec :=
  ![(X 0 0).re, (X 1 1).re, (X 2 2).re,
    (X 0 1).re, (X 0 1).im, (X 0 2).re, (X 0 2).im,
    (X 1 2).re, (X 1 2).im]

lemma square_add (x y : Four) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  revert x y
  decide +kernel

lemma square_square (x : Four) : (x ^ 2) ^ 2 = x := by
  revert x
  decide +kernel

lemma square_fixed_iff (x : Four) : x ^ 2 = x ↔ x.im = 0 := by
  revert x
  decide +kernel

lemma square_diag (r : ZMod 2) : (⟨r, 0⟩ : Four) ^ 2 = ⟨r, 0⟩ :=
  (square_fixed_iff _).mpr rfl

lemma encode_hermitian (c : Vec) (i j : Fin 3) : (encode c j i) ^ 2 = encode c i j := by
  fin_cases i <;> fin_cases j <;> simp [encode, square_square, square_diag]

lemma decode_encode (c : Vec) : decode (encode c) = c := by
  ext i
  fin_cases i <;> rfl

lemma encode_decode (X : Mat) (h : ∀ i j, (X j i) ^ 2 = X i j) :
    encode (decode X) = X := by
  have hd (i : Fin 3) : (X i i).im = 0 := (square_fixed_iff _).mp (h i i)
  have hd' (i : Fin 3) : (⟨(X i i).re, 0⟩ : Four) = X i i := by
    rw [← hd i]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [encode, decode, hd', h]

lemma encode_add (x y : Vec) : encode (x + y) = encode x + encode y := by
  funext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · exact square_add ⟨x 3, x 4⟩ ⟨y 3, y 4⟩
  · rfl
  · rfl
  · exact square_add ⟨x 5, x 6⟩ ⟨y 5, y 6⟩
  · exact square_add ⟨x 7, x 8⟩ ⟨y 7, y 8⟩
  · rfl

lemma decode_add (X Y : Mat) : decode (X + Y) = decode X + decode Y := by
  ext i
  fin_cases i <;> rfl

lemma equiv_sigma (x : Four) :
    HermitianTensorThree.sigma 1 (fieldEquiv x) = fieldEquiv (x ^ 2) := by
  change iterateFrobeniusEquiv (GaloisField 2 2) 2 1 (fieldEquiv x) = _
  rw [iterateFrobeniusEquiv_def]
  simp

/-- Coefficient transport through the fixed field equivalence used by the pair plane. -/
@[expose] public noncomputable def fourEntries (X : Models.HermitianSpace) : Mat :=
  X.val.map fieldEquiv.symm

lemma fourEntries_hermitian (X : Models.HermitianSpace) (i j : Fin 3) :
    (fourEntries X j i) ^ 2 = fourEntries X i j := by
  apply fieldEquiv.injective
  rw [← equiv_sigma]
  simpa [fourEntries] using HermitianTensorThree.entry_conjugate 1 X i j

/-- Hermitian diagonals have no imaginary coefficient; this follows from
Frobenius fixation of the actual native diagonal entries. -/
public theorem diagonal_im_eq_zero (X : Models.HermitianSpace) (i : Fin 3) :
    (fourEntries X i i).im = 0 :=
  (square_fixed_iff _).mp (fourEntries_hermitian X i i)

noncomputable def fromBinary (c : Vec) : Models.HermitianSpace :=
  ⟨(encode c).map fieldEquiv, by
    change HermitianTensorThree.adjoint 1 ((encode c).map fieldEquiv) = _
    funext i j
    change HermitianTensorThree.sigma 1 (fieldEquiv (encode c j i)) = _
    rw [equiv_sigma, encode_hermitian]
    rfl⟩

lemma fourEntries_fromBinary (c : Vec) : fourEntries (fromBinary c) = encode c := by
  funext i j
  exact fieldEquiv.symm_apply_apply _

lemma fromBinary_decode (X : Models.HermitianSpace) : fromBinary (decode (fourEntries X)) = X := by
  apply Subtype.ext
  change (encode (decode (fourEntries X))).map fieldEquiv = X.val
  rw [encode_decode _ (fourEntries_hermitian X)]
  funext i j
  exact fieldEquiv.apply_symm_apply _

noncomputable def coordAdd : Models.HermitianSpace →+ Vec where
  toFun X := decode (fourEntries X)
  map_zero' := by ext i; fin_cases i <;> simp [decode, fourEntries]
  map_add' X Y := by
    rw [show fourEntries (X + Y) = fourEntries X + fourEntries Y by
      funext i j
      exact map_add fieldEquiv.symm _ _]
    exact decode_add _ _

/-- Explicit coordinates of the actual native Hermitian space, in the stated order. -/
public noncomputable def binaryCoordinates : Models.HermitianSpace ≃ₗ[ZMod 2] Vec where
  toLinearMap := coordAdd.toZModLinearMap 2
  invFun := fromBinary
  left_inv := fromBinary_decode
  right_inv c := by
    change decode (fourEntries (fromBinary c)) = c
    rw [fourEntries_fromBinary, decode_encode]

public theorem binaryCoordinates_apply (X : Models.HermitianSpace) :
    binaryCoordinates X = decode (fourEntries X) := by rfl

public theorem encode_binaryCoordinates (X : Models.HermitianSpace) :
    encode (binaryCoordinates X) = fourEntries X :=
  encode_decode _ (fourEntries_hermitian X)

/-- The inverse coordinate map reconstructs exactly the explicit Hermitian matrix. -/
public theorem fourEntries_binaryCoordinates_symm (c : Vec) :
    fourEntries (binaryCoordinates.symm c) = encode c :=
  fourEntries_fromBinary c

/-- Conjugate transpose, executed by squaring coefficients in `Four`. -/
@[expose] public def adjointFour (A : Mat) : Mat := A.transpose.map (fun x => x ^ 2)

/-- Column matrix of `X ↦ A X σ(A)ᵀ` in the explicit nine coordinates. -/
@[expose] public def binaryMatrix (A : Matrix.SpecialLinearGroup (Fin 3) Four) :
    Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  fun i j => decode (A.val * encode (Pi.single j 1) * adjointFour A.val) i

def ruleAdd (A : Mat) : Vec →+ Vec where
  toFun c := decode (A * encode c * adjointFour A)
  map_zero' := by
    have hz : encode 0 = 0 := by funext i j; fin_cases i <;> fin_cases j <;> rfl
    simp only [hz, Matrix.mul_zero, Matrix.zero_mul]
    ext i
    fin_cases i <;> rfl
  map_add' x y := by
    rw [encode_add, Matrix.mul_add, Matrix.add_mul, decode_add]

/-- The executable matrix acts by the stated encode/action/decode rule. -/
public theorem binaryMatrix_mulVec (A : Matrix.SpecialLinearGroup (Fin 3) Four) (c : Vec) :
    decode (A.val * encode c * adjointFour A.val) = (binaryMatrix A).mulVec c := by
  exact (LinearMap.toMatrix'_mulVec ((ruleAdd A.val).toZModLinearMap 2) c).symm

lemma fourEntries_action (A : Matrix.SpecialLinearGroup (Fin 3) Four) (X : Models.HermitianSpace) :
    fourEntries (HermitianTensorThree.binaryAction 1
      (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A) X) =
      A.val * fourEntries X * adjointFour A.val := by
  change (A.val.map fieldEquiv * X.val *
    HermitianTensorThree.adjoint 1 (A.val.map fieldEquiv)).map fieldEquiv.symm = _
  rw [Matrix.map_mul, Matrix.map_mul]
  have ha : (A.val.map fieldEquiv).map fieldEquiv.symm = A.val := by
    funext i j
    exact fieldEquiv.symm_apply_apply _
  have hb : (HermitianTensorThree.adjoint 1 (A.val.map fieldEquiv)).map fieldEquiv.symm =
      adjointFour A.val := by
    funext i j
    change fieldEquiv.symm (HermitianTensorThree.sigma 1 (fieldEquiv (A.val j i))) = _
    rw [equiv_sigma, RingEquiv.symm_apply_apply]
    rfl
  rw [ha, hb]
  rfl

/-- The numerical rule agrees with the original descended tensor action. -/
public theorem binaryCoordinates_action (A : Matrix.SpecialLinearGroup (Fin 3) Four)
    (X : Models.HermitianSpace) :
    binaryCoordinates (HermitianTensorThree.binaryAction 1
      (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A) X) =
      (binaryMatrix A).mulVec (binaryCoordinates X) := by
  rw [binaryCoordinates_apply, fourEntries_action, ← encode_binaryCoordinates X, binaryMatrix_mulVec]

/-- Application to the native corrections: only the independent pair/SL lift
certificates remain; the binary-coordinate premise is discharged here. -/
public theorem correction_blocks
    (lifts : Fin 2 → Fin 22 → M23Geometry.pointwisePairStabilizer)
    (A : Fin 2 → Fin 22 → Matrix.SpecialLinearGroup (Fin 3) Four)
    (hlifts : ∀ j i, SixteenSubmodule.LocalBlocks.pairEmbedding (lifts j i) =
      SixteenSubmodule.LocalBlocks.explicitMarking *
        MathieuCode.m22Embedding (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i).val *
          SixteenSubmodule.LocalBlocks.explicitMarking⁻¹)
    (hA : ∀ j i, M23Geometry.PairPlane.pointwiseEquiv (lifts j i) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom (A j i)))
    (j : Fin 2) (i : Fin 22) (v : Models.HermitianSpace) :
    nativeCoordinates binaryCoordinates
      (Models.pointAction false (SixteenSubmodule.GeneratorMatrices.generatorCorrection j i) v) =
      (binaryMatrix (A j i)).mulVec (nativeCoordinates binaryCoordinates v) :=
  correction_blocks_of_sl_lifts binaryCoordinates binaryMatrix binaryCoordinates_action
    lifts A hlifts hA j i v

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison.HermitianCoordinates
