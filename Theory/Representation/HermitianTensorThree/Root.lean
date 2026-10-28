module
public import Theory.Representation.HermitianTensorThree
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic

/-!
# The marked root involution on the Hermitian tensor

The root is the literal matrix sending e₂ to e₂ + e₀. On the Hermitian
space its fixed vectors have last diagonal entry zero, entry (1,2) zero,
and entry (0,2) in the fixed field. The remaining coordinates consist of
three fixed-field entries and one extension-field entry. This gives the
fixed dimension 5n in H.4.4(2), without assuming a centralizer theorem.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.381.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree
open Matrix.PSL3Even.UnipotentGeometry
variable (n : ℕ) [NeZero n]

/-- The marked long-root parametrization. -/
def rootHom : Multiplicative (E n) →* Cover n :=
  (specialLinear (E n)).comp (central (E n))

def root : Cover n := rootHom n (Multiplicative.ofAdd 1)

omit [NeZero n] in
theorem root_matrix : (root n).val = !![1,0,1;0,1,0;0,0,1] := rfl

omit [NeZero n] in
theorem root_sq : root n ^ 2 = 1 := by
  rw [pow_two, root, ← map_mul]
  have h : Multiplicative.ofAdd (1 : E n) * Multiplicative.ofAdd 1 = 1 := by
    change Multiplicative.ofAdd (1 + 1 : E n) = Multiplicative.ofAdd 0
    congr 1
    exact CharTwo.add_self_eq_zero 1
  rw [h, map_one]

omit [NeZero n] in
theorem root_ne_one : root n ≠ 1 := by
  intro h
  have h02 := congrArg (fun g : Cover n => g.val 0 2) h
  exact one_ne_zero h02

omit [NeZero n] in
theorem orderOf_root : orderOf (root n) = 2 := orderOf_eq_prime (root_sq n) (root_ne_one n)

theorem root_action_iff (X : Space n) : action n (root n) X = X ↔
    X.val 2 2 = 0 ∧ X.val 1 2 = 0 ∧ sigma n (X.val 0 2) = X.val 0 2 := by
  have he (i j : Fin 3) := entry_conjugate n X i j
  constructor
  · intro h
    have h02 := congrArg (fun Y : Space n => Y.val 0 2) h
    have h01 := congrArg (fun Y : Space n => Y.val 0 1) h
    have h00 := congrArg (fun Y : Space n => Y.val 0 0) h
    simp only [action_apply, root_matrix, adjoint, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.mul_apply, Fin.sum_univ_three] at h02 h01 h00
    simp at h02 h01 h00
    have h12 : X.val 1 2 = 0 := by
      have hh := he 1 2
      rw [h01, map_zero] at hh
      exact hh.symm
    refine ⟨h02, h12, ?_⟩
    rw [he 2 0]
    rw [h02, add_zero] at h00
    have hz : X.val 2 0 + X.val 0 2 = 0 := by
      linear_combination h00
    exact CharTwo.add_eq_zero.mp hz
  · rintro ⟨h22,h12,h02⟩
    have h21 : X.val 2 1 = 0 := by rw [← he 2 1, h12, map_zero]
    have h20 : X.val 2 0 = X.val 0 2 := (he 2 0).symm.trans h02
    apply Subtype.ext
    rw [action_apply, root_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22, h12, h21, h20,
        CharTwo.add_self_eq_zero, add_assoc]

/-- Fixed vectors for the marked root in the descended representation. -/
def rootFixed : Submodule (F n) (Space n) :=
  LinearMap.ker (action n (root n) - LinearMap.id)

theorem mem_rootFixed (X : Space n) : X ∈ rootFixed n ↔ action n (root n) X = X := by
  change action n (root n) X - X = 0 ↔ _
  exact sub_eq_zero

theorem rootFixed_conditions (X : rootFixed n) :
    X.val.val 2 2 = 0 ∧ X.val.val 1 2 = 0 ∧
      sigma n (X.val.val 0 2) = X.val.val 0 2 :=
  (root_action_iff n X.val).mp ((mem_rootFixed n X.val).mp X.property)

/-- The root-fixed space has three fixed-field and one extension-field coordinate. -/
def rootFixedCoordinates : rootFixed n ≃ₗ[F n] ((Fin 3 → F n) × E n) where
  toFun X := (![⟨X.val.val 0 0, entry_conjugate n X.val 0 0⟩,
      ⟨X.val.val 1 1, entry_conjugate n X.val 1 1⟩,
      ⟨X.val.val 0 2, (rootFixed_conditions n X).2.2⟩], X.val.val 0 1)
  invFun v := ⟨(coordinates n).symm (![v.1 0,v.1 1,0], ![v.2,(v.1 2).val,0]), by
    rw [mem_rootFixed, root_action_iff]
    exact ⟨rfl,rfl,(v.1 2).property⟩⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    have h22 := (rootFixed_conditions n X).1
    have h12 := (rootFixed_conditions n X).2.1
    have h21 : X.val.val 2 1 = 0 := by
      rw [← entry_conjugate n X.val 2 1, h12, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinates, entry_conjugate, h22, h12, h21]
  right_inv v := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_add' X Y := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl
  map_smul' c X := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · rfl

theorem finrank_rootFixed : Module.finrank (F n) (rootFixed n) = 5 := by
  rw [(rootFixedCoordinates n).finrank_eq, Module.finrank_prod, finrank_E]
  simp

def binaryRootFixed : Submodule (ZMod 2) (Space n) :=
  LinearMap.ker (binaryAction n (root n) - LinearMap.id)

def binaryRootFixedEquiv : binaryRootFixed n ≃ rootFixed n where
  toFun X := ⟨X.val, X.property⟩
  invFun X := ⟨X.val, X.property⟩

theorem finrank_binaryRootFixed : Module.finrank (ZMod 2) (binaryRootFixed n) = 5 * n := by
  have hF := Module.natCard_eq_pow_finrank (K := F n) (V := rootFixed n)
  rw [card_F, finrank_rootFixed, ← pow_mul] at hF
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := binaryRootFixed n)
  have hc : Nat.card (ZMod 2) = 2 := by simp
  rw [hc, Nat.card_congr (binaryRootFixedEquiv n), hF] at h2
  have hh : n * 5 = Module.finrank (ZMod 2) (binaryRootFixed n) :=
    (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2
  omega

theorem finrank_binaryRootMoved :
    Module.finrank (ZMod 2)
      (LinearMap.range (binaryAction n (root n) - LinearMap.id)) = 4 * n := by
  have h := (binaryAction n (root n) - LinearMap.id).finrank_range_add_finrank_ker
  change _ + Module.finrank (ZMod 2) (binaryRootFixed n) =
    Module.finrank (ZMod 2) (Space n) at h
  rw [finrank_binaryRootFixed, finrank_binary] at h
  omega

end Representation.HermitianTensorThree
