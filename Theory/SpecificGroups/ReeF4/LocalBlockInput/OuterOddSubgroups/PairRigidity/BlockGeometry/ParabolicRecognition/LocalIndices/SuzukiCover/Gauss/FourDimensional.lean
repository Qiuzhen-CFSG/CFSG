module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Coordinates

/-!
# The explicit four-dimensional Suzuki Gauss calculation

The long, short, high and mixed B₂ elementary matrices reproduce exactly the
GLS3 four-root word under `SuzukiGaussData.standardPair`. Their signed words
are exchanged by the anti-diagonal Weyl matrix. The nonzero norm and reciprocal
identities from `Coordinates` prove the full Gauss factorization entrywise.
The literal middle Weyl word and the two coroot factors are checked as well.

These are comparison matrices: no representation of the full Ree carrier,
and no faithfulness of such a representation, is asserted here. The remaining
ambient calculation is the concrete `SuzukiGaussData.SplitIdentity` equation.

Source: GLS3, Table 2.4 type V and 2.3.4--8,
`refs/KGroup/GLS3/chapter2.tex`; the Suzuki coordinates of
Huppert--Blackburn III, XI.3.3, as formalized in
`BenderSuzuki/External/Huppert/XI/theorem_3_3.lean`.
-/

set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
open BlockParameters.FieldRecovery
variable {m : ℕ}

open BenderSuzuki.MatrixGroups
open scoped Matrix

/-- The four elementary positive B₂ root matrices, in long/short/high/mixed order. -/
def fourRoot (p : Bool) (i : Fin 4) (t : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  let M := ![!![1,0,0,0; 0,1,t,0; 0,0,1,0; 0,0,0,1],
    !![1,t,0,0; 0,1,0,0; 0,0,1,t; 0,0,0,1],
    !![1,0,0,t; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,t,0; 0,1,0,t; 0,0,1,0; 0,0,0,1]] i
  if p then M else M.transpose

def fourWord (p : Bool) (t u : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  fourRoot p 0 t * fourRoot p 1 (theta m t) * fourRoot p 2 u *
    fourRoot p 3 (t * theta m t + theta m u)

private theorem standard_matrix (a b : CoefficientField m) :
    SuzukiRootMatrix m a b =
      !![1,a,b,a^2 * titsEnd m a + a*b + titsEnd m b;
        0,1,titsEnd m a,a*titsEnd m a+b; 0,0,1,a; 0,0,0,1] := by
  simp only [SuzukiRootMatrix, pow_add, pow_one, titsEnd_apply]

theorem fourWord_positive (t u : CoefficientField m) :
    fourWord true t u = SuzukiRootMatrix m (standardPair (t,u)).1 (standardPair (t,u)).2 := by
  rw [standard_matrix]
  dsimp only [standardPair, Equiv.coe_fn_mk]
  simp only [map_add, map_mul, tits_theta]
  rw [← theta_sq (t := t)]
  have htwo : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWord, fourRoot, Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination -(t * (theta m t)^2) * htwo
  · ring

theorem fourWord_negative (t u : CoefficientField m) :
    fourWord false t u = SuzukiWeylMatrix m * fourWord true t u * SuzukiWeylMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWord, fourRoot, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- Expanded literal four-root word in the original GLS3 parameters. -/
theorem fourWord_positive_matrix (t u : CoefficientField m) :
    fourWord true t u =
      !![1,theta m t,t * theta m t + theta m u,norm t u;
        0,1,t,theta m u; 0,0,1,theta m t; 0,0,0,1] := by
  have htwo : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWord, fourRoot, Matrix.mul_apply, Fin.sum_univ_four]
  · unfold norm
    rw [← theta_sq (t := t)]
    ring
  · linear_combination (t * theta m t) * htwo

theorem fourWord_negative_matrix (t u : CoefficientField m) :
    fourWord false t u =
      !![1,0,0,0; theta m t,1,0,0; theta m u,t,1,0;
        norm t u,t * theta m t + theta m u,theta m t,1] := by
  rw [fourWord_negative, fourWord_positive_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- The diagonal factor in the four-dimensional Gauss identity. -/
def fourTorus (n : CoefficientField m) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  !![n,0,0,0; 0,titsEnd m n / n,0,0;
    0,0,n / titsEnd m n,0; 0,0,0,n⁻¹]

set_option maxHeartbeats 800000 in
theorem four_gauss (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    SuzukiWeylMatrix m * fourWord false t u =
      fourWord false (negativeFirst t u) (negativeSecond t u) *
        fourTorus (norm t u) * fourWord true (positiveFirst t u) (positiveSecond t u) := by
  rw [fourWord_negative_matrix, fourWord_negative_matrix, fourWord_positive_matrix,
    theta_negativeFirst, theta_negativeSecond, norm_negative t u hn,
    theta_positiveFirst, theta_positiveSecond, norm_positive t u hn]
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  dsimp only [positiveFirst, negativeFirst, negativeSecond]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, fourTorus, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hn, hM]
  all_goals try simp only [tits_norm, norm, map_add, map_mul, map_pow, tits_theta, titsEnd_twice]
  all_goals try simp only [← theta_sq (t := t), ← theta_sq (t := u)]
  all_goals ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

/-- The literal rank-one word on one of the two simple roots. -/
def fourWeyl (i : Fin 2) (a : CoefficientField m) :=
  fourRoot true (Fin.castLE (by decide : 2 ≤ 4) i) a *
    fourRoot false (Fin.castLE (by decide : 2 ≤ 4) i) a⁻¹ *
    fourRoot true (Fin.castLE (by decide : 2 ≤ 4) i) a

def fourCoroot (i : Fin 2) (a : (CoefficientField m)ˣ) :=
  fourWeyl i (a : CoefficientField m) * fourWeyl i 1

private theorem fourWeyl_long_one :
    fourWeyl (m := m) 0 1 = !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four, CharTwo.ofNat_eq_mod, CharTwo.add_self_eq_zero]

private theorem fourWeyl_short_one :
    fourWeyl (m := m) 1 1 = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four, CharTwo.ofNat_eq_mod, CharTwo.add_self_eq_zero]

/-- The representative is exactly the middle word [1,2,1,2]. -/
theorem four_panel_weyl :
    fourWeyl (m := m) 0 1 * fourWeyl 1 1 * fourWeyl 0 1 * fourWeyl 1 1 =
      SuzukiWeylMatrix m := by
  rw [fourWeyl_long_one, fourWeyl_short_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

private theorem fourCoroot_long (a : (CoefficientField m)ˣ) :
    fourCoroot 0 a = !![1,0,0,0; 0,(a : CoefficientField m),0,0;
      0,0,(a : CoefficientField m)⁻¹,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourCoroot, fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      a.ne_zero, CharTwo.add_self_eq_zero]

private theorem fourCoroot_short (a : (CoefficientField m)ˣ) :
    fourCoroot 1 a = !![(a : CoefficientField m),0,0,0; 0,(a : CoefficientField m)⁻¹,0,0;
      0,0,(a : CoefficientField m),0; 0,0,0,(a : CoefficientField m)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourCoroot, fourWeyl, fourRoot, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
      a.ne_zero, CharTwo.add_self_eq_zero]

/-- The diagonal factor uses the long coroot at π(n) and the short coroot at n. -/
theorem fourTorus_eq_coroots (n : (CoefficientField m)ˣ) :
    fourTorus (n : CoefficientField m) =
      fourCoroot 0 (Units.map (titsEnd m).toMonoidHom n) * fourCoroot 1 n := by
  rw [fourCoroot_long, fourCoroot_short]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourTorus, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, div_eq_mul_inv, mul_comm]

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
end
