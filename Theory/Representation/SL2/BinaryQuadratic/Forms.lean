module
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Theory.Representation.SL2.BinaryHermitianRecognition.Setup
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination
/-!
# Determinants and invariant forms for binary Frobenius pairs

The matrix-pair action preserves the determinant, whose polar form is
nondegenerate. Schur's lemma identifies every invariant bilinear form on an
irreducible algebraically closed representation with a scalar multiple of any
fixed nondegenerate invariant form. This gives exact polar normalization in
the SL₂ branch of Aschbacher--Smith G.4.1, printed p.342.
-/

public section
open scoped MatrixGroups
namespace Representation.SL2.BinaryQuadratic
open Representation.SL2.BinaryHermitian
open ClassicalOrthogonal.FourPlusMatrix
variable {K L : Type*} [Field K] [Field L]

theorem determinant_invariant [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) (g : SL(2,K)) (X : Mat (F := L)) :
    determinantForm (pair e s j g X) = determinantForm X := by
  rw [determinantForm_apply,determinantForm_apply,pair_apply,
    Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hf (k : ℕ) : (g.val.map (fun x => e x ^ 2^k)).det=1 := by
    have h := (Matrix.SpecialLinearGroup.map
      ((iterateFrobeniusEquiv L 2 k).toRingHom.comp e) g).det_coe
    convert h using 1
    congr 1
  have ha := hf j
  have hb := hf (j+s)
  rw [ha,hb,one_mul,mul_one]

theorem determinant_polar_nondegenerate :
    (determinantForm (F := L)).polarBilin.Nondegenerate := by
  have hleft : (determinantForm (F := L)).polarBilin.SeparatingLeft := by
    intro X hX
    have h00 := hX !![0,0;0,1]
    have h01 := hX !![0,0;1,0]
    have h10 := hX !![0,1;0,0]
    have h11 := hX !![1,0;0,0]
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      determinantForm_apply,Matrix.det_fin_two] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · change X 0 0=0; linear_combination h00
    · change X 0 1=0; linear_combination -h01
    · change X 1 0=0; linear_combination -h10
    · change X 1 1=0; linear_combination h11
  exact ⟨hleft,by
    intro X hX
    exact hleft X (fun Y => by rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]; exact hX Y)⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [IsAlgClosed L]

theorem invariant_form_scalar (ρ : Representation L G V) [ρ.IsIrreducible]
    (B : LinearMap.BilinForm L V) (hB : B.Nondegenerate)
    (hBinv : ∀ g v w, B (ρ g v) (ρ g w)=B v w)
    (C : LinearMap.BilinForm L V)
    (hCinv : ∀ g v w, C (ρ g v) (ρ g w)=C v w) :
    ∃ c : L, C=c•B := by
  let T : Module.End L V := (B.toDual hB).symm.toLinearMap.comp C
  have hT (v w : V) : B (T v) w = C v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (C v) w
  let f : ρ.IntertwiningMap ρ := {
    toLinearMap := T
    isIntertwining' g := by
      ext v
      apply (B.toDual hB).injective
      ext w
      obtain ⟨w,rfl⟩ := (ρ.apply_bijective g).surjective w
      change B (T (ρ g v)) (ρ g w)=B (ρ g (T v)) (ρ g w)
      rw [hT,hCinv,hBinv,hT] }
  obtain ⟨c,hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective f
  refine ⟨c,?_⟩
  ext v w
  have hf : c•v = T v := congrArg (fun f : ρ.IntertwiningMap ρ => f v) hc
  change C v w = c•B v w
  rw [←hT,←hf]
  simp only [map_smul,LinearMap.smul_apply]
end Representation.SL2.BinaryQuadratic
