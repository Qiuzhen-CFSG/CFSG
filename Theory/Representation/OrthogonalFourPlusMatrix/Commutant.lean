module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The scalar commutant of the determinant module

Every additive endomorphism commuting with the two SL₂ factors is a scalar.
Applying the natural SL₂ commutant theorem to each input/output column first
expresses the endomorphism as right multiplication. Commuting with the second
factor makes that matrix scalar. No assumption of field linearity is made.

This recovers the coefficient field inside the binary endomorphism ring for
Aschbacher--Smith 14.4.6(b), combined manuscript (1 March 2004), printed p.1008.
-/

public section
open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]
private def columnInsert (j : Fin 2) (v : Fin 2 → F) : Mat (F := F) :=
  fun i k => if k = j then v i else 0

private lemma columnInsert_left (A : Mat (F := F)) (j : Fin 2) (v : Fin 2 → F) :
    A * columnInsert j v = columnInsert j (A.mulVec v) := by
  ext i k
  fin_cases k <;> fin_cases j <;>
    simp [columnInsert, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The full additive commutant of the determinant action consists of field scalars. -/
theorem centralizer_scalar (f : Mat (F := F) →+ Mat (F := F))
    (hf : ∀ g : PairSL (F := F), ∀ M, f (matrixAction g M) = matrixAction g (f M)) :
    ∃ c : F, ∀ M, f M = c • M := by
  have hleft (A : SpecialLinearGroup (Fin 2) F) (M : Mat (F := F)) :
      f (A.val * M) = A.val * f M := by
    have h := hf (A, 1) M
    change f (A.val * M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val) =
      A.val * f M * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val at h
    simpa only [inv_one, SpecialLinearGroup.coe_one, mul_one] using h
  have hblock (j k : Fin 2) : ∃ c : F, ∀ v : Fin 2 → F,
      (fun i => f (columnInsert k v) i j) = c • v := by
    let b : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun v i => f (columnInsert k v) i j
        map_zero' := by
          have he : columnInsert k (0 : Fin 2 → F) = 0 := by ext i l; simp [columnInsert]
          change (fun i => f (columnInsert k 0) i j) = 0
          rw [he, f.map_zero]
          rfl
        map_add' := by
          intro v w
          have he : columnInsert k (v + w) = columnInsert k v + columnInsert k w := by
            ext i l
            by_cases h : l = k <;> simp [columnInsert, h]
          change (fun i => f (columnInsert k (v + w)) i j) = _
          rw [he, f.map_add]
          rfl }
    apply Representation.SL2NaturalOffenders.centralizer_scalar b
    intro A v
    change (fun i => f (columnInsert k (A.val.mulVec v)) i j) = _
    rw [← columnInsert_left, hleft]
    rfl
  choose c hc using hblock
  have hformula (M : Mat (F := F)) (i j : Fin 2) :
      f M i j = c j 0 * M i 0 + c j 1 * M i 1 := by
    have he : M = columnInsert 0 (fun i => M i 0) + columnInsert 1 (fun i => M i 1) := by
      ext i j
      fin_cases j <;> simp [columnInsert]
    have h0 := congrFun (hc j 0 (fun i => M i 0)) i
    have h1 := congrFun (hc j 1 (fun i => M i 1)) i
    conv_lhs => rw [he, map_add]
    exact congrArg₂ (· + ·) h0 h1
  let C : Mat (F := F) := fun i j => c j i
  have hformula' (M : Mat (F := F)) : f M = M * C := by
    ext i j
    rw [hformula]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp only [C]
    ring
  have hcomm (A : SpecialLinearGroup (Fin 2) F) : C * A.val = A.val * C := by
    have h := hf (1, A⁻¹) 1
    simpa [matrixAction, hformula'] using h.symm
  let b : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := C.mulVec
      map_zero' := Matrix.mulVec_zero C
      map_add' := Matrix.mulVec_add C }
  obtain ⟨a, ha⟩ := Representation.SL2NaturalOffenders.centralizer_scalar b (by
    intro A v
    change C.mulVec (A.val.mulVec v) = A.val.mulVec (C.mulVec v)
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec])
  have hC : C = a • 1 := by
    apply Matrix.mulVec_injective
    funext v
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ha v
  refine ⟨a, fun M => ?_⟩
  rw [hformula', hC, Matrix.mul_smul, mul_one]
end ClassicalOrthogonal.FourPlusMatrix
