module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.Matrices

/-!
# The two matrix blocks in the linear dihedral centralizer

Assume a linear map preserves the fixed pair (0,5) and commutes with the
literal D₁₀ generators. Comparing rotation and reflection on each natural
pair kills the off-diagonal entries within that pair. The rotation's second
column then kills maps from the moved coordinates into the fixed pair.
Linearity extends the resulting basis formulas to all vectors.

The fixed-pair premise is discharged in `Factorization` by the actual
`dihedralLift_fixed_iff`, before this matrix calculation is applied.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization

local instance : CharP GoldenFour 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GoldenFour).injective 2

private def tau : F := fieldEquiv goldenFourTau

private theorem tau_ne_zero : tau ≠ 0 := by
  change fieldEquiv goldenFourTau ≠ 0
  rw [map_ne_zero]
  decide +kernel

private def rotate (v : Fin 6 → F) : Fin 6 → F :=
  ![v 0,v 2,v 1 + tau * v 2,v 4,v 3 + tau * v 4,v 5]

private def reflect (v : Fin 6 → F) : Fin 6 → F :=
  ![v 0,v 2,v 1,v 4,v 3,v 5]

private theorem rotate_formula (v : Fin 6 → F) :
    blockAction (slEquiv rotation) v = rotate v := by
  funext i
  fin_cases i <;> simp [blockAction, slEquiv_rotation, rotate, tau]

private theorem reflect_formula (v : Fin 6 → F) :
    blockAction (slEquiv (flip : SL(2,GoldenFour))) v = reflect v := by
  have hm : (slEquiv (flip : SL(2,GoldenFour))).val = !![0,1;1,0] := by
    change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) GoldenFour).map fieldEquiv = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  funext i
  fin_cases i <;> simp [blockAction, hm, reflect]

private theorem zero_of_add_tau (x b : F) (h : b + tau * x = b) : x = 0 :=
  (mul_eq_zero.mp (add_left_cancel (h.trans (add_zero b).symm))).resolve_left tau_ne_zero

private theorem pair_shape (w z : Fin 6 → F)
    (hr : z = rotate w) (hj : z = reflect w) (hs : w + tau • z = rotate z) :
    w = ![0,w 1,0,w 3,0,0] ∧ z = ![0,0,w 1,0,w 3,0] := by
  have h2 : w 1 + tau * w 2 = w 1 := congrFun (hr.symm.trans hj) 2
  have h4 : w 3 + tau * w 4 = w 3 := congrFun (hr.symm.trans hj) 4
  have h0 : w 0 + tau * w 0 = w 0 := by simpa [hj, rotate, reflect] using congrFun hs 0
  have h5 : w 5 + tau * w 5 = w 5 := by simpa [hj, rotate, reflect] using congrFun hs 5
  have hz2 := zero_of_add_tau _ _ h2
  have hz4 := zero_of_add_tau _ _ h4
  have hz0 := zero_of_add_tau _ _ h0
  have hz5 := zero_of_add_tau _ _ h5
  constructor
  · funext i
    fin_cases i <;> simp [hz2, hz4, hz0, hz5]
  · rw [hj]
    funext i
    fin_cases i <;> simp [reflect, hz2, hz4, hz0, hz5]

private theorem rotate_first (i : Fin 2) (a : F) :
    rotate (Pi.single (![1,3] i) a) = Pi.single (![2,4] i) a := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [rotate]

private theorem reflect_first (i : Fin 2) (a : F) :
    reflect (Pi.single (![1,3] i) a) = Pi.single (![2,4] i) a := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [reflect]

private theorem rotate_second (i : Fin 2) (a : F) :
    rotate (Pi.single (![2,4] i) a) =
      Pi.single (![1,3] i) a + tau • Pi.single (![2,4] i) a := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [rotate]

theorem linear_centralizer_blockForm (f : (Fin 6 → F) →ₗ[F] (Fin 6 → F))
    (hfixed : ∀ v : Fin 6 → F, v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 →
      f v 1 = 0 ∧ f v 2 = 0 ∧ f v 3 = 0 ∧ f v 4 = 0)
    (hf : ∀ (d : DihedralGroup 5) (v : Fin 6 → F),
      f (blockAction (slEquiv (dihedralModel d)) v) =
        blockAction (slEquiv (dihedralModel d)) (f v)) :
    ∀ v, f v = matrixAction (coefficients f) v := by
  have hr (v : Fin 6 → F) : f (rotate v) = rotate (f v) := by
    simpa only [dihedralModel_rotation, rotate_formula] using hf (.r 1) v
  have hj (v : Fin 6 → F) : f (reflect v) = reflect (f v) := by
    simpa only [dihedralModel_reflection, reflect_formula] using hf (.sr 0) v
  have hfix (j : Fin 6) (hj : j = 0 ∨ j = 5) :
      f (Pi.single j 1) = ![f (Pi.single j 1) 0,0,0,0,0,f (Pi.single j 1) 5] := by
    have hz := hfixed (Pi.single j 1) (by
      rcases hj with rfl | rfl <;> simp)
    funext i
    fin_cases i <;> simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  have hpair (i : Fin 2) :
      f (Pi.single (![1,3] i) 1) =
        ![0,f (Pi.single (![1,3] i) 1) 1,0,f (Pi.single (![1,3] i) 1) 3,0,0] ∧
      f (Pi.single (![2,4] i) 1) =
        ![0,0,f (Pi.single (![1,3] i) 1) 1,0,f (Pi.single (![1,3] i) 1) 3,0] := by
    apply pair_shape
    · rw [← hr, rotate_first]
    · rw [← hj, reflect_first]
    · rw [← hr, rotate_second, map_add, map_smul]
  have hbase (j : Fin 6) : f (Pi.single j 1) = matrixAction (coefficients f) (Pi.single j 1) := by
    fin_cases j
    · simpa [matrixAction, coefficients] using hfix 0 (Or.inl rfl)
    · simpa [matrixAction, coefficients] using (hpair 0).1
    · simpa [matrixAction, coefficients] using (hpair 0).2
    · simpa [matrixAction, coefficients] using (hpair 1).1
    · simpa [matrixAction, coefficients] using (hpair 1).2
    · simpa [matrixAction, coefficients] using hfix 5 (Or.inr rfl)
  intro v
  have hv : v = ∑ j : Fin 6, v j • Pi.single j (1 : F) := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm
  rw [hv, map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, hbase, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [matrixAction, coefficients, Fin.sum_univ_six] <;> ring

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
