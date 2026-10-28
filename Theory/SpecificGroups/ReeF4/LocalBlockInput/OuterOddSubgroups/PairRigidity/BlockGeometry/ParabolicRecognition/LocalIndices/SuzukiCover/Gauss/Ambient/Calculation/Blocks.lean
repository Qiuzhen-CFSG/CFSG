module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Tables
public import Mathlib.Data.Matrix.Block

/-!
# Full coordinate decomposition for the Suzuki Gauss calculation

The four signed middle simple-root curves preserve thirteen coordinate blocks:
one of dimension 12, four of dimension 5, four of dimension 4, and four lines.
The explicit inverse coordinate table proves that these blocks exhaust all 52
coordinates. The linear and quadratic support tables have no cross-block entries.
Consequently all literal root, Weyl, panel and torus words decompose in the same
matrix algebra equivalence. `gauss_of_blocks` assembles the thirteen equations;
it is a conditional reduction, not an assertion of the remaining block identities.

Source: GLS3, Table 2.4 type V and 2.3.4--8, `refs/KGroup/GLS3/chapter2.tex`;
the complete coefficient tables in `Ambient.Tables`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
open BlockParameters.FieldRecovery
open scoped Matrix

abbrev blockSize : Fin 13 → ℕ := ![12,5,5,5,5,4,4,4,4,1,1,1,1]
instance (b : Fin 13) : NeZero (blockSize b) := ⟨by fin_cases b <;> decide⟩

def blockCoord (b : Fin 13) : Fin (blockSize b) → Fin 52 :=
  match b with
  | 0 => ![0,1,2,3,24,25,26,27,28,29,30,31]
  | 1 => ![5,6,7,8,9]
  | 2 => ![19,20,21,22,23]
  | 3 => ![32,33,34,35,36]
  | 4 => ![46,47,48,49,50]
  | 5 => ![11,12,13,14]
  | 6 => ![15,16,17,18]
  | 7 => ![37,38,39,40]
  | 8 => ![41,42,43,44]
  | 9 => ![4]
  | 10 => ![10]
  | 11 => ![45]
  | 12 => ![51]

abbrev BlockIndex := (b : Fin 13) × Fin (blockSize b)
def blockLookup : Fin 52 → BlockIndex :=
  ![⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨9,0⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨10,0⟩, ⟨5,0⟩, ⟨5,1⟩, ⟨5,2⟩, ⟨5,3⟩, ⟨6,0⟩, ⟨6,1⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨2,0⟩, ⟨2,1⟩, ⟨2,2⟩, ⟨2,3⟩, ⟨2,4⟩, ⟨0,4⟩, ⟨0,5⟩, ⟨0,6⟩, ⟨0,7⟩, ⟨0,8⟩, ⟨0,9⟩, ⟨0,10⟩, ⟨0,11⟩, ⟨3,0⟩, ⟨3,1⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨8,0⟩, ⟨8,1⟩, ⟨8,2⟩, ⟨8,3⟩, ⟨11,0⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨4,3⟩, ⟨4,4⟩, ⟨12,0⟩]

def coordEquiv : BlockIndex ≃ Fin 52 where
  toFun x := blockCoord x.1 x.2
  invFun := blockLookup
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma support_owners : ∀ (p : Bool) (i : Fin 2),
    (linearSupport (simpleIndex p i) ++ quadraticSupport (simpleIndex p i)).all
      (fun rc => decide ((blockLookup rc.1).1 = (blockLookup rc.2).1)) = true := by
  decide +kernel

lemma support_same_block (p : Bool) (i : Fin 2) (b c : Fin 13)
    (r : Fin (blockSize b)) (s : Fin (blockSize c))
    (h : (blockCoord b r, blockCoord c s) ∈ linearSupport (simpleIndex p i) ∨
      (blockCoord b r, blockCoord c s) ∈ quadraticSupport (simpleIndex p i)) : b = c := by
  have hx := List.all_eq_true.mp (support_owners p i)
    (blockCoord b r, blockCoord c s) (List.mem_append.mpr h)
  have he : (blockLookup (blockCoord b r)).1 = (blockLookup (blockCoord c s)).1 :=
    of_decide_eq_true hx
  change (coordEquiv.symm (coordEquiv ⟨b,r⟩)).1 =
    (coordEquiv.symm (coordEquiv ⟨c,s⟩)).1 at he
  simpa only [Equiv.symm_apply_apply] using he

noncomputable section
variable {R : Type*} [CommRing R]
def blockSimple (b : Fin 13) (p : Bool) (i : Fin 2) (t : R) :
    Matrix (Fin (blockSize b)) (Fin (blockSize b)) R :=
  (simpleMatrix p i t).submatrix (blockCoord b) (blockCoord b)

def decompose : Matrix (Fin 52) (Fin 52) R ≃+* Matrix BlockIndex BlockIndex R :=
  Matrix.reindexRingEquiv R coordEquiv.symm

lemma decompose_simple (p : Bool) (i : Fin 2) (t : R) :
    decompose (simpleMatrix p i t) = Matrix.blockDiagonal' (fun b => blockSimple b p i t) := by
  ext ⟨b,r⟩ ⟨c,s⟩
  change simpleMatrix p i t (blockCoord b r) (blockCoord c s) = _
  by_cases h : b = c
  · subst c
    rw [Matrix.blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    have he : blockCoord b r ≠ blockCoord c s := by
      intro he
      have hx : (⟨b,r⟩ : BlockIndex) = ⟨c,s⟩ := coordEquiv.injective he
      exact h (congrArg Sigma.fst hx)
    have hl : (blockCoord b r, blockCoord c s) ∉ linearSupport (simpleIndex p i) :=
      fun hx => h (support_same_block p i b c r s (Or.inl hx))
    have hq : (blockCoord b r, blockCoord c s) ∉ quadraticSupport (simpleIndex p i) :=
      fun hx => h (support_same_block p i b c r s (Or.inr hx))
    simp [simpleMatrix, incidence, he, hl, hq]
end
noncomputable section
variable {R : Type*} [Field R]

def blockWeyl (b : Fin 13) (i : Fin 2) (t : R) :=
  blockSimple b true i t * blockSimple b false i t⁻¹ * blockSimple b true i t

def blockReflection (b : Fin 13) (i : Fin 2) :
    Matrix (Fin (blockSize b)) (Fin (blockSize b)) R := blockWeyl b i 1

def blockRoot (b : Fin 13) (p : Bool) (i : Fin 4) (t : R) :=
  ![blockSimple b p 0 t, blockSimple b p 1 t,
    blockReflection b 1 * blockSimple b p 0 t * blockReflection b 1,
    blockReflection b 0 * blockSimple b p 1 t * blockReflection b 0] i

def blockPanel (b : Fin 13) : Matrix (Fin (blockSize b)) (Fin (blockSize b)) R :=
  blockReflection b 0 * blockReflection b 1 * blockReflection b 0 * blockReflection b 1

lemma decompose_weyl (i : Fin 2) (t : R) :
    decompose (weylMatrix i t) = Matrix.blockDiagonal' (fun b => blockWeyl b i t) := by
  simp only [weylMatrix, map_mul, decompose_simple, ← Matrix.blockDiagonal'_mul, blockWeyl]

lemma decompose_reflection (i : Fin 2) :
    decompose (reflectionMatrix (R := R) i) =
      Matrix.blockDiagonal' (fun b => blockReflection b i) := decompose_weyl i 1

lemma decompose_root (p : Bool) (i : Fin 4) (t : R) :
    decompose (rootMatrix p i t) = Matrix.blockDiagonal' (fun b => blockRoot b p i t) := by
  fin_cases i <;> simp [rootMatrix, blockRoot, decompose_simple,
    decompose_reflection, ← Matrix.blockDiagonal'_mul]

lemma decompose_panel : decompose (panelMatrix (R := R)) =
    Matrix.blockDiagonal' (fun b => blockPanel b) := by
  simp only [panelMatrix, blockPanel, map_mul, decompose_reflection, ← Matrix.blockDiagonal'_mul]

variable {m : ℕ}
def blockWord (b : Fin 13) (p : Bool) (t u : CoefficientField m) :=
  blockRoot b p 0 t * blockRoot b p 1 (theta m t) * blockRoot b p 2 u *
    blockRoot b p 3 (t * theta m t + theta m u)

def blockTorus (b : Fin 13) (n : (CoefficientField m)ˣ) :=
  (blockWeyl b 0 (titsEnd m (n : CoefficientField m)) * blockReflection b 0) *
    (blockWeyl b 1 (n : CoefficientField m) * blockReflection b 1)

lemma decompose_word (p : Bool) (t u : CoefficientField m) :
    decompose (wordMatrix p t u) = Matrix.blockDiagonal' (fun b => blockWord b p t u) := by
  simp only [wordMatrix, blockWord, map_mul, decompose_root, ← Matrix.blockDiagonal'_mul]

lemma decompose_torus (n : (CoefficientField m)ˣ) :
    decompose (torusMatrix n) = Matrix.blockDiagonal' (fun b => blockTorus b n) := by
  simp only [torusMatrix, blockTorus, map_mul, decompose_weyl, decompose_reflection,
    ← Matrix.blockDiagonal'_mul]

/-- The Gauss equation on one invariant coordinate block. -/
def BlockGauss (m : ℕ) (b : Fin 13) : Prop :=
  ∀ (t u : CoefficientField m) (hn : norm t u ≠ 0),
    blockPanel b * blockWord b false t u =
      blockWord b false (negativeFirst t u) (negativeSecond t u) *
        blockTorus b (Units.mk0 (norm t u) hn) *
          blockWord b true (positiveFirst t u) (positiveSecond t u)

/-- The block equations cover every entry of the original 52-dimensional equation. -/
lemma gauss_of_blocks (h : ∀ b, BlockGauss m b) : GaussIdentity m := by
  intro t u hn
  apply (decompose (R := CoefficientField m)).injective
  simp only [map_mul, decompose_panel, decompose_word, decompose_torus,
    ← Matrix.blockDiagonal'_mul]
  exact congrArg Matrix.blockDiagonal' (funext fun b => h b t u hn)
end
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
end
