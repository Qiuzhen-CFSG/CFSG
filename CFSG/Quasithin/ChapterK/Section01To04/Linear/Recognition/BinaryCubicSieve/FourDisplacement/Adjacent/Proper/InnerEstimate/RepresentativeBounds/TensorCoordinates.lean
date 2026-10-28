module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.TensorModel

/-!
# The proper adjacent highest line in the mixed tensor

The three positive simple-root equations and the inactive root-2 exchange
force all coordinates except e₀ ⊗ (e₀ ∧ e₁) to vanish. Over F₂ this identifies
every nonzero highest vector with that seed. The action-on-seed formula then
reduces its translates to columns of the genuine natural–exterior tensor matrix.

These calculations support the involution bounds without assuming absolute
irreducibility or a module catalogue. Source application: Aschbacher–Smith
K.3.2, printed pp.454–455; Guralnick–Malle, Classification of 2F-modules II,
author manuscript Proposition 4.7, pp.25–26. The tensor and compound-matrix
construction and its ATLAS attribution are retained in the imported model.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RepresentativeBounds
open Representation
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open SupportSeparation
open Atlas.Order20160A8.Bivectors
open scoped BigOperators Kronecker MatrixGroups

/-- The tensor e₀ ⊗ (e₀ ∧ e₁). -/
def seed : Space := Pi.single (0, 0) 1

/-- Acting on the seed selects one column of the literal tensor matrix. -/
theorem act_seed (g : Group) :
    mixedTensor g seed = fun p => tensorMatrix g p (0, 0) := by
  change (tensorMatrix g).mulVec (Pi.single (0, 0) 1) = _
  rw [Matrix.mulVec_single_one]
  rfl

private theorem swap2_matrix : (simpleSwap 2).val =
    !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0] := by decide

/-- The proper adjacent highest space in the mixed tensor is the seed line. -/
theorem highest_eq_smul_seed (x : Space)
    (h : LocalHighestVector mixedTensor {0, 1} x) : x = x (0, 0) • seed := by
  have u0 := h.upper_fixed 0 1 (by decide)
  have u1 := h.upper_fixed 1 2 (by decide)
  have u2 := h.upper_fixed 2 3 (by decide)
  have s2 := h.inactive_fixed 2 (by decide)
  have h0 := congrFun u0 (0,0)
  have h1 := congrFun u0 (0,1)
  have h2 := congrFun u0 (0,2)
  have h3 := congrFun u0 (0,3)
  have h4 := congrFun u0 (0,4)
  have h5 := congrFun u0 (0,5)
  have h6 := congrFun u0 (2,1)
  have h7 := congrFun u0 (2,2)
  have h8 := congrFun u0 (3,1)
  have h9 := congrFun u0 (3,2)
  have h10 := congrFun u1 (0,0)
  have h11 := congrFun u1 (0,4)
  have h12 := congrFun u1 (1,0)
  have h13 := congrFun u1 (1,1)
  have h14 := congrFun u1 (1,2)
  have h15 := congrFun u1 (1,4)
  have h16 := congrFun u1 (3,0)
  have h17 := congrFun u1 (3,4)
  have h18 := congrFun u2 (0,1)
  have h19 := congrFun u2 (0,3)
  have h20 := congrFun u2 (2,0)
  have h21 := congrFun u2 (2,1)
  have h22 := congrFun s2 (0,3)
  simp [mixedTensor, tensorMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.kroneckerMap,
    compound, first, second, swap2_matrix,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  have hx03 : x (0,3) = 0 := h22.symm.trans h19
  have hx11 : x (1,1) = 0 := by simpa [h10, hx03, h3] using h1
  have hx12 : x (1,2) = 0 := by simpa [h18, h19, h4] using h2
  have hx20 : x (2,0) = 0 := by simpa [h0, hx11, h13] using h12
  have hx25 : x (2,5) = 0 := by simpa [h4, h5, h7] using h15
  have hx32 : x (3,2) = 0 := by simpa [h13, h14, h16] using h21
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [seed, h0, h10, h18, hx03, h19, h11, hx11, hx12,
      h3, h4, h5, hx20, h13, h14, h6, h7, hx25, h20, h16, hx32, h8, h9, h17]

/-- Over the binary field the seed line has just one nonzero vector. -/
theorem highest_eq_seed (x : Space) (hx : x ≠ 0)
    (h : LocalHighestVector mixedTensor {0, 1} x) : x = seed := by
  have he := highest_eq_smul_seed x h
  have hc : x (0, 0) ≠ 0 := by
    intro hz
    exact hx (by simpa [hz] using he)
  have hone : x (0, 0) = 1 := by
    have hh : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact hh _ hc
  simpa [hone] using he

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.RepresentativeBounds
