module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Blocks
/-!
# Repeated blocks and fixed lines in the complete Suzuki matrices

The four five-dimensional blocks have the same coefficients, as do the four
four-dimensional blocks and the four lines. Finite checks compare both support
tables under the order-preserving coordinate bijections; the induced matrix
algebra equivalences then compare all the prescribed words. Thus
`gauss_of_representatives` reduces the full equation to blocks 0, 1, 5 and 9.
The representative line is fixed by every root curve, proving `blockGauss_nine`.

Source: GLS3, Table 2.4 type V, `refs/KGroup/GLS3/chapter2.tex`, and the
full coefficient tables in `Ambient.Tables`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
open BlockParameters.FieldRecovery
open scoped Matrix
noncomputable section

def representative : Fin 13 → Fin 13 := ![0,1,1,1,1,5,5,5,5,9,9,9,9]
lemma size_representative (b : Fin 13) : blockSize (representative b) = blockSize b := by
  fin_cases b <;> decide

def representativeEquiv (b : Fin 13) :
    Fin (blockSize (representative b)) ≃ Fin (blockSize b) := finCongr (size_representative b)

def representativeMap {R : Type*} [CommRing R] (b : Fin 13) :
    Matrix (Fin (blockSize (representative b))) (Fin (blockSize (representative b))) R ≃+*
      Matrix (Fin (blockSize b)) (Fin (blockSize b)) R :=
  Matrix.reindexRingEquiv R (representativeEquiv b)

set_option maxRecDepth 4096 in
lemma representative_coefficients : ∀ (b : Fin 13) (p : Bool) (i : Fin 2)
    (r s : Fin (blockSize b)),
    (blockCoord b r = blockCoord b s ↔
      blockCoord (representative b) ((representativeEquiv b).symm r) =
        blockCoord (representative b) ((representativeEquiv b).symm s)) ∧
    ((blockCoord b r, blockCoord b s) ∈ linearSupport (simpleIndex p i) ↔
      (blockCoord (representative b) ((representativeEquiv b).symm r),
        blockCoord (representative b) ((representativeEquiv b).symm s)) ∈
          linearSupport (simpleIndex p i)) ∧
    ((blockCoord b r, blockCoord b s) ∈ quadraticSupport (simpleIndex p i) ↔
      (blockCoord (representative b) ((representativeEquiv b).symm r),
        blockCoord (representative b) ((representativeEquiv b).symm s)) ∈
          quadraticSupport (simpleIndex p i)) := by
  decide +kernel

lemma blockSimple_representative {R : Type*} [CommRing R] (b : Fin 13)
    (p : Bool) (i : Fin 2) (t : R) :
    blockSimple b p i t = representativeMap b (blockSimple (representative b) p i t) := by
  ext r s
  change simpleMatrix p i t (blockCoord b r) (blockCoord b s) =
    simpleMatrix p i t
      (blockCoord (representative b) ((representativeEquiv b).symm r))
      (blockCoord (representative b) ((representativeEquiv b).symm s))
  obtain ⟨he, hl, hq⟩ := representative_coefficients b p i r s
  simp only [simpleMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul, incidence, he, hl, hq]

variable {R : Type*} [Field R]
lemma blockWeyl_representative (b : Fin 13) (i : Fin 2) (t : R) :
    blockWeyl b i t = representativeMap b (blockWeyl (representative b) i t) := by
  simp only [blockWeyl, map_mul, blockSimple_representative b]

lemma blockReflection_representative (b : Fin 13) (i : Fin 2) :
    blockReflection (R := R) b i = representativeMap b (blockReflection (representative b) i) :=
  blockWeyl_representative b i 1

lemma blockRoot_representative (b : Fin 13) (p : Bool) (i : Fin 4) (t : R) :
    blockRoot b p i t = representativeMap b (blockRoot (representative b) p i t) := by
  fin_cases i <;> simp [blockRoot, map_mul, blockSimple_representative b,
    blockReflection_representative b]

lemma blockPanel_representative (b : Fin 13) :
    blockPanel (R := R) b = representativeMap b (blockPanel (representative b)) := by
  simp only [blockPanel, map_mul, blockReflection_representative b]

variable {m : ℕ}
lemma blockWord_representative (b : Fin 13) (p : Bool) (t u : CoefficientField m) :
    blockWord b p t u = representativeMap b (blockWord (representative b) p t u) := by
  simp only [blockWord, map_mul, blockRoot_representative b]

lemma blockTorus_representative (b : Fin 13) (n : (CoefficientField m)ˣ) :
    blockTorus b n = representativeMap b (blockTorus (representative b) n) := by
  simp only [blockTorus, map_mul, blockWeyl_representative b, blockReflection_representative b]

lemma blockGauss_of_representative (b : Fin 13) (h : BlockGauss m (representative b)) :
    BlockGauss m b := by
  intro t u hn
  simp only [blockPanel_representative b, blockWord_representative b,
    blockTorus_representative b, ← map_mul]
  exact congrArg (representativeMap b) (h t u hn)

public lemma gauss_of_representatives (h0 : BlockGauss m 0) (h1 : BlockGauss m 1)
    (h5 : BlockGauss m 5) (h9 : BlockGauss m 9) : GaussIdentity m := by
  apply gauss_of_blocks
  intro b
  apply blockGauss_of_representative
  fin_cases b <;> first | exact h0 | exact h1 | exact h5 | exact h9

lemma blockSimple_nine {R : Type*} [CommRing R] (p : Bool) (i : Fin 2) (t : R) :
    blockSimple 9 p i t = 1 := by
  ext r c
  fin_cases r
  fin_cases c
  cases p <;> fin_cases i <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport]

lemma blockWeyl_nine (i : Fin 2) (t : R) : blockWeyl 9 i t = 1 := by
  simp only [blockWeyl, blockSimple_nine, one_mul]

lemma blockReflection_nine (i : Fin 2) : blockReflection (R := R) 9 i = 1 :=
  blockWeyl_nine i 1

lemma blockRoot_nine (p : Bool) (i : Fin 4) (t : R) : blockRoot 9 p i t = 1 := by
  fin_cases i
  · exact blockSimple_nine p 0 t
  · exact blockSimple_nine p 1 t
  · change blockReflection 9 1 * blockSimple 9 p 0 t * blockReflection 9 1 = _
    simp only [blockReflection_nine, blockSimple_nine, one_mul]
  · change blockReflection 9 0 * blockSimple 9 p 1 t * blockReflection 9 0 = _
    simp only [blockReflection_nine, blockSimple_nine, one_mul]

public lemma blockGauss_nine (m : ℕ) : BlockGauss m 9 := by
  intro t u hn
  simp only [blockPanel, blockWord, blockTorus, blockReflection_nine,
    blockRoot_nine, blockWeyl_nine, one_mul]
end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
