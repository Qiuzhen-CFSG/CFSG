module

public import Theory.Representation.HermitianTensorThree

/-!
# The field involution on the descended SL₃ tensor

Coefficient conjugation on the Hermitian fixed space equals transposition.
Its fixed matrices are the symmetric matrices over the fixed field, of
dimension six. Rank-nullity gives moved dimension three. The coefficient
involution conjugates the actual SL₃ action by the field automorphism.

These are the direct calculations in H.4.4(6), Aschbacher–Smith, combined
manuscript of 1 March 2004, printed p.381. Coverage of all outer involutions,
pointwise centralizers and the three quotient actions are separate results.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree

variable (n : ℕ) [NeZero n]

/-- Coefficient conjugation, expressed as transposition on Hermitian matrices. -/
def fieldSwap : Space n ≃ₗ[F n] Space n where
  toFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate n X j i⟩
  invFun X := ⟨X.val.transpose, by
    ext i j
    exact entry_conjugate n X j i⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fieldSwap_apply (X : Space n) : (fieldSwap n X).val = X.val.transpose := rfl

/-- This is the source's coefficient-field automorphism on V. -/
theorem fieldSwap_eq_map (X : Space n) : (fieldSwap n X).val = X.val.map (sigma n) := by
  ext i j
  exact (entry_conjugate n X j i).symm

theorem fieldSwap_sq : fieldSwap n * fieldSwap n = 1 := by
  ext X i j
  rfl

/-- Conjugation by the field involution retains the original cover homomorphism. -/
theorem fieldSwap_action (g : Cover n) (X : Space n) :
    fieldSwap n (action n g X) =
      action n (Matrix.SpecialLinearGroup.map (sigma n).toRingHom g) (fieldSwap n X) := by
  apply Subtype.ext
  change (g.val * X.val * adjoint n g.val).transpose =
    g.val.map (sigma n) * X.val.transpose * adjoint n (g.val.map (sigma n))
  have h : adjoint n (g.val.map (sigma n)) = g.val.transpose := by
    ext i j
    exact sigma_involutive n (g.val j i)
  rw [h, Matrix.transpose_mul, Matrix.transpose_mul]
  exact (Matrix.mul_assoc _ _ _).symm

/-- The fixed subspace for the actual field involution. -/
def fieldFixed : Submodule (F n) (Space n) :=
  LinearMap.ker ((fieldSwap n).toLinearMap - LinearMap.id)

theorem mem_fieldFixed (X : Space n) :
    X ∈ fieldFixed n ↔ fieldSwap n X = X := by
  change fieldSwap n X - X = 0 ↔ _
  exact sub_eq_zero

theorem fieldFixed_entry (X : fieldFixed n) (i j : Fin 3) :
    sigma n (X.val.val i j) = X.val.val i j := by
  have h := (mem_fieldFixed n X.val).mp X.property
  have hij := congrArg (fun Y : Space n => Y.val i j) h
  exact (entry_conjugate n X.val j i).trans hij

/-- All six independent symmetric entries lie in the actual fixed subfield. -/
def fieldFixedCoordinates : fieldFixed n ≃ₗ[F n] ((Fin 3 → F n) × (Fin 3 → F n)) where
  toFun X := (fun i => ⟨X.val.val i i, fieldFixed_entry n X i i⟩,
    ![⟨X.val.val 0 1, fieldFixed_entry n X 0 1⟩,
      ⟨X.val.val 0 2, fieldFixed_entry n X 0 2⟩,
      ⟨X.val.val 1 2, fieldFixed_entry n X 1 2⟩])
  invFun v := ⟨(coordinates n).symm (v.1, fun i => (v.2 i).val), by
    rw [mem_fieldFixed]
    apply Subtype.ext
    rw [fieldSwap_apply]
    have hf (c : F n) : sigma n c.val = c.val := c.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinates, hf]⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinates, entry_conjugate]
  right_inv v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl
  map_smul' c X := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl

theorem finrank_fieldFixed : Module.finrank (F n) (fieldFixed n) = 6 := by
  rw [(fieldFixedCoordinates n).finrank_eq, Module.finrank_prod]
  simp

theorem finrank_fieldMoved :
    Module.finrank (F n)
      (LinearMap.range ((fieldSwap n).toLinearMap - LinearMap.id)) = 3 := by
  have h := ((fieldSwap n).toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  change _ + Module.finrank (F n) (fieldFixed n) = Module.finrank (F n) (Space n) at h
  rw [finrank_fieldFixed, finrank_space] at h
  omega

theorem fieldSwap_ne_one : fieldSwap n ≠ 1 := by
  intro h
  have hzero : (fieldSwap n).toLinearMap - LinearMap.id = 0 := by rw [h]; exact sub_self _
  have hm := finrank_fieldMoved n
  rw [hzero, LinearMap.range_zero] at hm
  simp at hm

/-- Forget the fixed-field scalars while retaining the same invertible map. -/
def binaryEquiv (e : Space n ≃ₗ[F n] Space n) : Space n ≃ₗ[ZMod 2] Space n where
  toFun := e
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply
  map_add' := e.map_add
  map_smul' := e.toLinearMap.toAddMonoidHom.toZModLinearMap 2 |>.map_smul

def binaryEquivHom : (Space n ≃ₗ[F n] Space n) →* (Space n ≃ₗ[ZMod 2] Space n) where
  toFun := binaryEquiv n
  map_one' := by apply LinearEquiv.ext; intro X; rfl
  map_mul' _ _ := by apply LinearEquiv.ext; intro X; rfl

def binaryActionHom : Cover n →* (Space n ≃ₗ[ZMod 2] Space n) :=
  (binaryEquivHom n).comp (actionHom n)

def binaryImage : Subgroup (Space n ≃ₗ[ZMod 2] Space n) := (binaryActionHom n).range

/-- The complete binary linear normalizer; source overgroups are subgroups of this. -/
def binaryNormalizer : Subgroup (Space n ≃ₗ[ZMod 2] Space n) :=
  Subgroup.normalizer (binaryImage n : Set (Space n ≃ₗ[ZMod 2] Space n))

def fieldSwapBinary : Space n ≃ₗ[ZMod 2] Space n := binaryEquiv n (fieldSwap n)

def binaryFieldFixed : Submodule (ZMod 2) (Space n) :=
  LinearMap.ker ((fieldSwapBinary n).toLinearMap - LinearMap.id)

/-- Restriction of scalars does not change which vectors the involution fixes. -/
def binaryFieldFixedEquiv : binaryFieldFixed n ≃ fieldFixed n where
  toFun X := ⟨X.val, X.property⟩
  invFun X := ⟨X.val, X.property⟩

theorem finrank_binaryFieldFixed : Module.finrank (ZMod 2) (binaryFieldFixed n) = 6 * n := by
  have hF := Module.natCard_eq_pow_finrank (K := F n) (V := fieldFixed n)
  rw [card_F, finrank_fieldFixed, ← pow_mul] at hF
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := binaryFieldFixed n)
  have hc : Nat.card (ZMod 2) = 2 := by simp
  rw [hc, Nat.card_congr (binaryFieldFixedEquiv n), hF] at h2
  have hh : n * 6 = Module.finrank (ZMod 2) (binaryFieldFixed n) :=
    (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2
  omega

theorem finrank_binaryFieldMoved :
    Module.finrank (ZMod 2)
      (LinearMap.range ((fieldSwapBinary n).toLinearMap - LinearMap.id)) = 3 * n := by
  have h := ((fieldSwapBinary n).toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  change _ + Module.finrank (ZMod 2) (binaryFieldFixed n) =
    Module.finrank (ZMod 2) (Space n) at h
  rw [finrank_binaryFieldFixed, finrank_binary] at h
  omega

end Representation.HermitianTensorThree
