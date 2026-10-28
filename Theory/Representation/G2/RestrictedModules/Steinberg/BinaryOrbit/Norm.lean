module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction

open scoped TensorProduct BigOperators
/-!
# The norm of the binary G₂ orbit

The sum of the 64 translates factors as the ordered product of the six
operators `1 + x_α(1)` applied to the lowest vector. The Weyl formulas identify
that lowest vector; six sparse tensor calculations then give the specified seed.
All calculations take place over the arbitrary characteristic-two field, using
the actual root action on the six-coordinate natural module. No numerical rank
computation or classification theorem enters this proof.

Source: GLS3, 2.8.7 and Example 2.8.10(g), with the root conventions from the
attributed ATLAS G₂ port. The tensor orbit is specified in `Steinberg.Construction`.
-/

public noncomputable section
namespace Atlas.G2.Restricted.Steinberg
open NaturalCoordinates
variable (F : Type*) [Field F] [CharP F 2]

private theorem sum_bool_cons {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → Bool) → M) :
    ∑ t, f t = ∑ a : Bool, ∑ t : Fin n → Bool, f (Fin.cons a t) := by
  calc
    _ = ∑ ab : Bool × (Fin n → Bool), f (Fin.cons ab.1 ab.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm _ _
        (fun t => congrArg f (Fin.cons_self_tail t).symm)
    _ = _ := Fintype.sum_prod_type _

private theorem sum_six {R : Type*} [NonAssocSemiring R]
    (a b c d e f : Bool → R) :
    (∑ t : BinaryIndex, a (t 0) * b (t 1) * c (t 2) * d (t 3) * e (t 4) * f (t 5)) =
      (a true + a false) * (b true + b false) * (c true + c false) *
        (d true + d false) * (e true + e false) * (f true + f false) := by
  simp only [sum_bool_cons, show @Fin.cons 5 (fun _ => Bool) = Matrix.vecCons from rfl,
    show @Fin.cons 4 (fun _ => Bool) = Matrix.vecCons from rfl,
    show @Fin.cons 3 (fun _ => Bool) = Matrix.vecCons from rfl,
    show @Fin.cons 2 (fun _ => Bool) = Matrix.vecCons from rfl,
    show @Fin.cons 1 (fun _ => Bool) = Matrix.vecCons from rfl,
    show @Fin.cons 0 (fun _ => Bool) = Matrix.vecCons from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fintype.sum_unique]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Fintype.sum_bool]

private theorem action_longest (v : NaturalCoordinates.Space F) :
    NaturalCoordinates.action F (longestWeyl F) v = ![v 5,v 4,v 3,v 2,v 1,v 0] := by
  simp [longestWeyl, pow_succ, map_mul, Module.End.mul_apply]

private theorem lowest : ambientAction F (longestWeyl F) (seed F) =
    pure F (e F 5) (e F 5) (e F 4) + pure F (e F 5) (e F 4) (e F 5) := by
  have h0 : NaturalCoordinates.action F (longestWeyl F) (e F 0) = e F 5 := by
    ext i; fin_cases i <;> simp [action_longest, e]
  have h1 : NaturalCoordinates.action F (longestWeyl F) (e F 1) = e F 4 := by
    ext i; fin_cases i <;> simp [action_longest, e]
  simp [seed, h0, h1]

private theorem norm_factorization : (∑ t : BinaryIndex, binaryOrbitVector F t) =
    ((ambientAction F (rootA 1) + 1) * (ambientAction F (rootB 1) + 1) *
      (ambientAction F (rootC 1) + 1) * (ambientAction F (rootD 1) + 1) *
      (ambientAction F (rootE 1) + 1) * (ambientAction F (rootF 1) + 1))
      (ambientAction F (longestWeyl F) (seed F)) := by
  have hh := sum_six
    (fun b => ambientAction F (rootA (if b then 1 else 0)))
    (fun b => ambientAction F (rootB (if b then 1 else 0)))
    (fun b => ambientAction F (rootC (if b then 1 else 0)))
    (fun b => ambientAction F (rootD (if b then 1 else 0)))
    (fun b => ambientAction F (rootE (if b then 1 else 0)))
    (fun b => ambientAction F (rootF (if b then 1 else 0)))
  simp only [Bool.false_eq_true, ↓reduceIte, rootA_zero, rootB_zero, rootC_zero,
    rootD_zero, rootE_zero, rootF_zero, map_one] at hh
  have he := congrArg
    (fun a : Module.End F (Ambient F) => a (ambientAction F (longestWeyl F) (seed F))) hh
  simpa only [binaryOrbitVector, unipotentProduct, binaryParameters, map_mul,
    Module.End.mul_apply, LinearMap.sum_apply] using he

private theorem rootA_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootA 1) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3, e F 4 + e F 0, e F 5 + e F 1] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private theorem rootB_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootB 1) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3 + e F 0, e F 4, e F 5 + e F 2] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private theorem rootC_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootC 1) (e F i) =
      ![e F 0, e F 1, e F 2, e F 3 + e F 1, e F 4 + e F 2, e F 5 + e F 0] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private theorem rootD_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootD 1) (e F i) =
      ![e F 0, e F 1, e F 2 + e F 0, e F 3, e F 4 + e F 1, e F 5 + e F 3] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private theorem rootE_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootE 1) (e F i) =
      ![e F 0, e F 1, e F 2 + e F 1, e F 3, e F 4 + e F 3, e F 5] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private theorem rootF_basis (i : Fin 6) :
    NaturalCoordinates.action F (rootF 1) (e F i) =
      ![e F 0, e F 1 + e F 0, e F 2, e F 3 + e F 2, e F 4, e F 5 + e F 4] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [e]

private def norm0 : Ambient F :=
  pure F (e F 5) (e F 4) (e F 5) +
      pure F (e F 5) (e F 5) (e F 4)

private def norm1 : Ambient F :=
  pure F (e F 4) (e F 4) (e F 5) +
      pure F (e F 4) (e F 5) (e F 4)

private theorem norm_step_F :
    (ambientAction F (rootF 1) + 1) (norm0 F) = norm1 F := by
  rw [← one_smul F ((ambientAction F (rootF 1) + 1) (norm0 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm0, norm1,
    map_add, ambientAction_pure, rootF_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals simp only [CharTwo.two_eq_zero]

private def norm2 : Ambient F :=
  pure F (e F 3) (e F 3) (e F 5) +
      pure F (e F 3) (e F 4) (e F 5) +
      pure F (e F 3) (e F 5) (e F 3) +
      pure F (e F 3) (e F 5) (e F 4) +
      pure F (e F 4) (e F 3) (e F 5) +
      pure F (e F 4) (e F 5) (e F 3)

private theorem norm_step_E :
    (ambientAction F (rootE 1) + 1) (norm1 F) = norm2 F := by
  rw [← one_smul F ((ambientAction F (rootE 1) + 1) (norm1 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm1, norm2,
    map_add, ambientAction_pure, rootE_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals simp only [CharTwo.two_eq_zero]

private def norm3 : Ambient F :=
  pure F (e F 1) (e F 3) (e F 5) +
      pure F (e F 1) (e F 5) (e F 3) +
      pure F (e F 3) (e F 1) (e F 3) +
      pure F (e F 3) (e F 1) (e F 5) +
      pure F (e F 3) (e F 3) (e F 1) +
      pure F (e F 3) (e F 3) (e F 4) +
      pure F (e F 3) (e F 4) (e F 3) +
      pure F (e F 3) (e F 5) (e F 1)

private theorem norm_step_D :
    (ambientAction F (rootD 1) + 1) (norm2 F) = norm3 F := by
  rw [← one_smul F ((ambientAction F (rootD 1) + 1) (norm2 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm2, norm3,
    map_add, ambientAction_pure, rootD_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals simp only [CharTwo.two_eq_zero]

private def norm4 : Ambient F :=
  pure F (e F 1) (e F 0) (e F 3) +
      pure F (e F 1) (e F 1) (e F 2) +
      pure F (e F 1) (e F 1) (e F 3) +
      pure F (e F 1) (e F 1) (e F 4) +
      pure F (e F 1) (e F 2) (e F 1) +
      pure F (e F 1) (e F 2) (e F 3) +
      pure F (e F 1) (e F 3) (e F 0) +
      pure F (e F 1) (e F 3) (e F 1) +
      pure F (e F 1) (e F 3) (e F 2) +
      pure F (e F 1) (e F 3) (e F 4) +
      pure F (e F 1) (e F 4) (e F 1) +
      pure F (e F 1) (e F 4) (e F 3) +
      pure F (e F 3) (e F 0) (e F 1) +
      pure F (e F 3) (e F 1) (e F 0) +
      pure F (e F 3) (e F 1) (e F 2) +
      pure F (e F 3) (e F 1) (e F 4) +
      pure F (e F 3) (e F 2) (e F 1) +
      pure F (e F 3) (e F 2) (e F 3) +
      pure F (e F 3) (e F 3) (e F 2) +
      pure F (e F 3) (e F 4) (e F 1)

private theorem norm_step_C :
    (ambientAction F (rootC 1) + 1) (norm3 F) = norm4 F := by
  rw [← one_smul F ((ambientAction F (rootC 1) + 1) (norm3 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm3, norm4,
    map_add, ambientAction_pure, rootC_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals simp only [CharTwo.two_eq_zero]

private def norm5 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 1) +
      pure F (e F 0) (e F 0) (e F 2) +
      pure F (e F 0) (e F 1) (e F 0) +
      pure F (e F 0) (e F 1) (e F 2) +
      pure F (e F 0) (e F 1) (e F 4) +
      pure F (e F 0) (e F 2) (e F 0) +
      pure F (e F 0) (e F 2) (e F 1) +
      pure F (e F 0) (e F 2) (e F 3) +
      pure F (e F 0) (e F 3) (e F 2) +
      pure F (e F 0) (e F 4) (e F 1) +
      pure F (e F 1) (e F 0) (e F 1) +
      pure F (e F 1) (e F 0) (e F 2) +
      pure F (e F 1) (e F 0) (e F 4) +
      pure F (e F 1) (e F 1) (e F 0) +
      pure F (e F 1) (e F 2) (e F 0) +
      pure F (e F 1) (e F 4) (e F 0) +
      pure F (e F 3) (e F 0) (e F 2) +
      pure F (e F 3) (e F 2) (e F 0)

private theorem norm_step_B :
    (ambientAction F (rootB 1) + 1) (norm4 F) = norm5 F := by
  rw [← one_smul F ((ambientAction F (rootB 1) + 1) (norm4 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm4, norm5,
    map_add, ambientAction_pure, rootB_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals simp only [CharTwo.two_eq_zero]

private def norm6 : Ambient F :=
  pure F (e F 0) (e F 0) (e F 1) +
      pure F (e F 0) (e F 1) (e F 0)

private theorem norm_step_A :
    (ambientAction F (rootA 1) + 1) (norm5 F) = norm6 F := by
  rw [← one_smul F ((ambientAction F (rootA 1) + 1) (norm5 F))]
  simp only [LinearMap.add_apply, Module.End.one_apply, norm5, norm6,
    map_add, ambientAction_pure, rootA_basis, Matrix.cons_val]
  simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  match_scalars
  all_goals norm_num
  all_goals linear_combination (CharTwo.two_eq_zero (R := F))

/-- The actual binary-unipotent norm is the chosen highest vector. -/
theorem sum_binaryOrbitVector : (∑ t : BinaryIndex, binaryOrbitVector F t) = seed F := by
  rw [norm_factorization]
  have hlow : ambientAction F (longestWeyl F) (seed F) = norm0 F := by
    rw [lowest]
    exact add_comm _ _
  simp only [Module.End.mul_apply, hlow, norm_step_F, norm_step_E, norm_step_D,
    norm_step_C, norm_step_B, norm_step_A]
  rfl

end Atlas.G2.Restricted.Steinberg
