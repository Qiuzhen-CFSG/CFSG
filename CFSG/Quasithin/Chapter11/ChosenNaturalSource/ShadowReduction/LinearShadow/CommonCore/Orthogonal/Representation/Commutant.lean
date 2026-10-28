module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.GroupTheory.IsPerfect

/-!
# Recovering the second matrix factor from its original additive action

An additive map commuting with the natural SL₂ action on both columns is
right multiplication by its value at the identity matrix. Thus a commuting
perfect group acts through a uniquely determined special linear right factor.
The determinant-one conclusion follows from perfectness, without presuming
linearity over the coefficient field. The kernel is exactly the original
action kernel, and coordinate transport retains that kernel.

This is the local algebra used to recognize the action on P in
Aschbacher--Smith, combined manuscript, printed p.774. The coefficient field
comes from the K-marking and need not agree with the original field on V.
-/

public noncomputable section
open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OrthogonalRepresentation
variable {F : Type*} [Field F]
private def columnInsert (j : Fin 2) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  fun i k => if k = j then v i else 0
private lemma columnInsert_left (A : Matrix (Fin 2) (Fin 2) F) (j : Fin 2) (v : Fin 2 → F) :
    A * columnInsert j v = columnInsert j (A.mulVec v) := by
  ext i k
  fin_cases k <;> fin_cases j <;>
    simp [columnInsert, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem left_commutant (f : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hf : ∀ (A : SL(2,F)) M, f (A.val * M) = A.val * f M) :
    ∀ M, f M = M * f 1 := by
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
    rw [← columnInsert_left, hf]
    rfl
  choose c hc using hblock
  have hformula (M : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
      f M i j = c j 0 * M i 0 + c j 1 * M i 1 := by
    have he : M = columnInsert 0 (fun i => M i 0) + columnInsert 1 (fun i => M i 1) := by
      ext i j
      fin_cases j <;> simp [columnInsert]
    have h0 := congrFun (hc j 0 (fun i => M i 0)) i
    have h1 := congrFun (hc j 1 (fun i => M i 1)) i
    conv_lhs => rw [he, map_add]
    exact congrArg₂ (· + ·) h0 h1
  let C : Matrix (Fin 2) (Fin 2) F := fun i j => c j i
  have hformula' (M : Matrix (Fin 2) (Fin 2) F) : f M = M * C := by
    ext i j
    rw [hformula, Matrix.mul_apply, Fin.sum_univ_two]
    dsimp only [C]
    ring
  intro M
  rw [hformula' M, hformula' 1, one_mul]

variable {J : Type*} [Group J]
    (a : J →* Multiplicative (AddAut (Matrix (Fin 2) (Fin 2) F)))
    (ha : ∀ j (A : SL(2,F)) M, (a j).toAdd (A.val * M) = A.val * (a j).toAdd M)

def rightMatrix : J →* Matrix (Fin 2) (Fin 2) F where
  toFun j := (a j⁻¹).toAdd 1
  map_one' := by simp
  map_mul' j k := by
    change (a (j * k)⁻¹).toAdd 1 = (a j⁻¹).toAdd 1 * (a k⁻¹).toAdd 1
    rw [_root_.mul_inv_rev, map_mul]
    change (a k⁻¹).toAdd ((a j⁻¹).toAdd 1) = _
    exact left_commutant (a k⁻¹).toAdd.toAddMonoidHom (ha k⁻¹) _

theorem rightMatrix_det [Group.IsPerfect J] (j : J) :
    Matrix.det (rightMatrix a ha j) = 1 := by
  let f := (Matrix.detMonoidHom.comp (rightMatrix a ha)).toHomUnits
  have hf : f j = 1 := Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator
  exact congrArg Units.val hf

def rightSL [Group.IsPerfect J] : J →* SL(2,F) where
  toFun j := ⟨rightMatrix a ha j, rightMatrix_det a ha j⟩
  map_one' := Subtype.ext (rightMatrix a ha).map_one
  map_mul' j k := Subtype.ext ((rightMatrix a ha).map_mul j k)

theorem rightSL_action [Group.IsPerfect J] (j : J) (M : Matrix (Fin 2) (Fin 2) F) :
    (a j).toAdd M = M * (rightSL a ha j)⁻¹.val := by
  have hval : (rightSL a ha j)⁻¹.val = (a j).toAdd 1 := by
    rw [← map_inv]
    change (a j⁻¹⁻¹).toAdd 1 = (a j).toAdd 1
    rw [inv_inv]
  rw [hval]
  exact left_commutant (a j).toAdd.toAddMonoidHom (ha j) M

theorem rightSL_ker [Group.IsPerfect J] : (rightSL a ha).ker = a.ker := by
  ext j
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hj
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro M
    change (a j).toAdd M = M
    have hh := rightSL_action a ha j M
    simpa only [hj, inv_one, SpecialLinearGroup.coe_one, mul_one] using hh
  · intro hj
    apply Subtype.ext
    change (a j⁻¹).toAdd 1 = 1
    rw [map_inv, hj, inv_one]
    rfl

variable {P : Type*} [Group P]

def inCoordinates (e : P ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (r : J →* MulAut P) : J →* Multiplicative (AddAut (Matrix (Fin 2) (Fin 2) F)) where
  toFun j := Multiplicative.ofAdd (AddEquiv.toMultiplicative.symm ((MulAut.congr e) (r j)))
  map_one' := by rw [map_one, map_one]; rfl
  map_mul' j k := by rw [map_mul, map_mul]; rfl

theorem inCoordinates_apply (e : P ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (r : J →* MulAut P) (j : J) (M : Matrix (Fin 2) (Fin 2) F) :
    (inCoordinates e r j).toAdd M = (e (r j (e.symm (Multiplicative.ofAdd M)))).toAdd := by rfl

theorem inCoordinates_ker (e : P ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (r : J →* MulAut P) : (inCoordinates e r).ker = r.ker := by
  ext j
  change Multiplicative.ofAdd (AddEquiv.toMultiplicative.symm ((MulAut.congr e) (r j))) = 1 ↔ r j = 1
  constructor
  · intro hj
    have hh : (MulAut.congr e) (r j) = 1 := by
      apply AddEquiv.toMultiplicative.symm.injective
      exact congrArg Multiplicative.toAdd hj
    exact (MulAut.congr e).injective (hh.trans (MulAut.congr e).map_one.symm)
  · rintro hj
    rw [hj, map_one]
    rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OrthogonalRepresentation
