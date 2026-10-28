module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The descended twisted tensor of the natural SL₃ module

The field `E` is GF(2^(2n)), `F` is the actual fixed subfield of its n-th
Frobenius, and the two factors are the natural representation and its
coefficient twist. The tensor is identified with matrices by
`x ⊗ y ↦ (xᵢ yⱼ)`. Semilinear interchange becomes conjugate transposition;
its fixed matrices carry the descended action `X ↦ g X σ(g)ᵀ`.
Three fixed diagonal entries and three arbitrary extension-field entries
provide coordinates for this space, proving dimensions 9 over F and 9n
in characteristic two. The image group acts faithfully by its literal
inclusion in the linear group. Identifying its kernel and the normalizer
requires further theorems, not an order comparison.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.4.2 setup and H.4.4, printed pp.380–381.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
namespace Representation.HermitianTensorThree

abbrev E (n : ℕ) := OrthogonalFourMinus.FiniteModel.Field n
abbrev F (n : ℕ) := OrthogonalFourMinus.FiniteModel.fixedField n
abbrev sigma (n : ℕ) := OrthogonalFourMinus.FiniteModel.conjugation n
abbrev sigmaAlg (n : ℕ) := OrthogonalFourMinus.FiniteModel.conjugationAlg n

variable (n : ℕ) [NeZero n]

theorem card_E : Nat.card (E n) = 2 ^ (2 * n) :=
  GaloisField.card 2 (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n))

theorem card_F : Nat.card (F n) = 2 ^ n :=
  OrthogonalFourMinus.FiniteModel.card_fixedField n

theorem sigma_involutive : Function.Involutive (sigma n) :=
  OrthogonalFourMinus.FiniteModel.conjugation_involutive n

theorem finrank_E : Module.finrank (F n) (E n) = 2 :=
  OrthogonalFourMinus.FiniteModel.finrank_field n

abbrev Natural := Fin 3 → E n
abbrev Cover := Matrix.SpecialLinearGroup (Fin 3) (E n)
abbrev Tensor := Natural n ⊗[E n] Natural n
abbrev Mat := Matrix (Fin 3) (Fin 3) (E n)

/-- The original natural action, on column vectors. -/
def naturalAction : Representation (E n) (Cover n) (Natural n) := specialLinearNatural 3

/-- The Galois conjugate has the same carrier and conjugated matrix entries. -/
def conjugateAction : Representation (E n) (Cover n) (Natural n) :=
  (naturalAction n).comp (Matrix.SpecialLinearGroup.map (sigma n).toRingHom)

/-- The actual tensor product of the natural representation and its twist. -/
def tensorAction : Representation (E n) (Cover n) (Tensor n) :=
  (naturalAction n).tprod (conjugateAction n)

/-- Coordinates retain the order of the two tensor factors. -/
def tensorCoordinates : Tensor n ≃ₗ[E n] Mat n :=
  (TensorProduct.comm (E n) (Natural n) (Natural n)).trans
    (TensorProduct.piScalarRight (E n) (E n) (Natural n) (Fin 3))

omit [NeZero n] in
theorem tensorCoordinates_tmul (x y : Natural n) :
    tensorCoordinates n (x ⊗ₜ[E n] y) = Matrix.vecMulVec x y := by
  ext i j
  change (TensorProduct.piScalarRight (E n) (E n) (Natural n) (Fin 3))
    (y ⊗ₜ[E n] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Matrix expression for the semilinear interchange. -/
def adjoint (X : Mat n) : Mat n := X.transpose.map (sigma n)

omit [NeZero n] in
theorem adjoint_add (X Y : Mat n) : adjoint n (X + Y) = adjoint n X + adjoint n Y := by
  ext i j
  exact map_add (sigma n) _ _

omit [NeZero n] in
theorem adjoint_smul (c : E n) (X : Mat n) :
    adjoint n (c • X) = sigma n c • adjoint n X := by
  ext i j
  exact map_mul (sigma n) _ _

omit [NeZero n] in
theorem adjoint_mul (X Y : Mat n) : adjoint n (X * Y) = adjoint n Y * adjoint n X := by
  simp only [adjoint, Matrix.transpose_mul, Matrix.map_mul]

omit [NeZero n] in
theorem adjoint_one : adjoint n (1 : Mat n) = 1 := by simp [adjoint]

theorem adjoint_involutive : Function.Involutive (adjoint n) := by
  intro X
  ext i j
  exact sigma_involutive n (X i j)

/-- The map γ on the actual tensor product, not a replacement carrier. -/
def gamma (u : Tensor n) : Tensor n :=
  (tensorCoordinates n).symm (adjoint n (tensorCoordinates n u))

omit [NeZero n] in
theorem gamma_add (u v : Tensor n) : gamma n (u + v) = gamma n u + gamma n v := by
  simp [gamma, adjoint_add]

omit [NeZero n] in
theorem gamma_smul (c : E n) (u : Tensor n) :
    gamma n (c • u) = sigma n c • gamma n u := by
  simp [gamma, adjoint_smul]

theorem gamma_involutive : Function.Involutive (gamma n) := by
  intro u
  simp only [gamma, LinearEquiv.apply_symm_apply, adjoint_involutive n _,
    LinearEquiv.symm_apply_apply]

omit [NeZero n] in
theorem gamma_tmul (x y : Natural n) :
    gamma n (x ⊗ₜ[E n] y) =
      (fun i => sigma n (y i)) ⊗ₜ[E n] (fun i => sigma n (x i)) := by
  apply (tensorCoordinates n).injective
  simp only [gamma, LinearEquiv.apply_symm_apply, tensorCoordinates_tmul]
  ext i j
  simp [adjoint, Matrix.vecMulVec, mul_comm]

/-- Tensor action in matrix coordinates. -/
def matrixAction : Representation (E n) (Cover n) (Mat n) where
  toFun g := {
    toFun X := g.val * X * adjoint n g.val
    map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intros; simp }
  map_one' := by ext X i j; simp [adjoint_one]
  map_mul' g h := by
    ext X i j
    change ((g * h).val * X * adjoint n (g * h).val) i j =
      (g.val * (h.val * X * adjoint n h.val) * adjoint n g.val) i j
    rw [Matrix.SpecialLinearGroup.coe_mul, adjoint_mul]
    simp only [Matrix.mul_assoc]

omit [NeZero n] in
theorem matrixAction_apply (g : Cover n) (X : Mat n) :
    matrixAction n g X = g.val * X * adjoint n g.val := rfl

omit [NeZero n] in
theorem tensorCoordinates_action (g : Cover n) (u : Tensor n) :
    tensorCoordinates n (tensorAction n g u) = matrixAction n g (tensorCoordinates n u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | tmul x y =>
    change tensorCoordinates n (naturalAction n g x ⊗ₜ[E n] conjugateAction n g y) = _
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, matrixAction_apply,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    change (g.val.map (sigma n)).mulVec y = Matrix.vecMul y (adjoint n g.val)
    exact (Matrix.vecMul_transpose (g.val.map (sigma n)) y).symm

theorem adjoint_action (g : Cover n) (X : Mat n) :
    adjoint n (matrixAction n g X) = matrixAction n g (adjoint n X) := by
  rw [matrixAction_apply, adjoint_mul, adjoint_mul, adjoint_involutive n,
    matrixAction_apply, Matrix.mul_assoc]

/-- γ commutes with the genuine SL₃ tensor action. -/
theorem gamma_action (g : Cover n) (u : Tensor n) :
    gamma n (tensorAction n g u) = tensorAction n g (gamma n u) := by
  apply (tensorCoordinates n).injective
  simp only [gamma, LinearEquiv.apply_symm_apply, tensorCoordinates_action, adjoint_action]

/-- The fixed space is a subrepresentation over the actual fixed field. -/
def hermitian : Subrepresentation (restrictScalars (k := F n) (matrixAction n)) where
  toSubmodule := {
    carrier := {X | adjoint n X = X}
    zero_mem' := by ext i j; exact map_zero (sigma n)
    add_mem' := by
      intro X Y hX hY
      change adjoint n (X + Y) = X + Y
      rw [adjoint_add, hX, hY]
    smul_mem' := by
      intro c X hX
      change adjoint n (c • X) = c • X
      have h : adjoint n (c • X) = c • adjoint n X := by
        ext i j
        exact (sigmaAlg n).toLinearMap.map_smul c (X j i)
      rw [h, hX] }
  apply_mem_toSubmodule := by
    intro g X hX
    change adjoint n (matrixAction n g X) = matrixAction n g X
    rw [adjoint_action, hX]

/-- Matrix coordinates for V = C_U(γ). -/
abbrev Space := (hermitian n).toSubmodule

def action : Representation (F n) (Cover n) (Space n) := (hermitian n).toRepresentation

theorem action_apply (g : Cover n) (X : Space n) :
    (action n g X).val = g.val * X.val * adjoint n g.val := rfl

def fixedTensor : Submodule (F n) (Tensor n) :=
  (hermitian n).toSubmodule.comap ((tensorCoordinates n).restrictScalars (F n)).toLinearMap

theorem mem_fixedTensor (u : Tensor n) : u ∈ fixedTensor n ↔ gamma n u = u := by
  change adjoint n (tensorCoordinates n u) = tensorCoordinates n u ↔ _
  rw [gamma, LinearEquiv.symm_apply_eq]

/-- The explicit identification with the fixed space on the tensor itself. -/
def fixedTensorEquiv : fixedTensor n ≃ₗ[F n] Space n where
  toFun u := ⟨tensorCoordinates n u.val, u.property⟩
  invFun X := ⟨(tensorCoordinates n).symm X.val, by
    change adjoint n (tensorCoordinates n ((tensorCoordinates n).symm X.val)) =
      tensorCoordinates n ((tensorCoordinates n).symm X.val)
    rw [LinearEquiv.apply_symm_apply]
    exact X.property⟩
  left_inv u := by apply Subtype.ext; exact (tensorCoordinates n).symm_apply_apply u.val
  right_inv X := by apply Subtype.ext; exact (tensorCoordinates n).apply_symm_apply X.val
  map_add' u v := by apply Subtype.ext; exact map_add (tensorCoordinates n) _ _
  map_smul' c u := by
    apply Subtype.ext
    exact ((tensorCoordinates n).restrictScalars (F n)).map_smul c u.val

theorem entry_conjugate (X : Space n) (i j : Fin 3) :
    sigma n (X.val j i) = X.val i j := congrFun (congrFun X.property i) j

/-- Three fixed diagonal coordinates and the three upper off-diagonal entries. -/
def coordinates : Space n ≃ₗ[F n] ((Fin 3 → F n) × (Fin 3 → E n)) where
  toFun X := ((fun i => ⟨X.val i i, entry_conjugate n X i i⟩),
    ![X.val 0 1, X.val 0 2, X.val 1 2])
  invFun v := ⟨!![(v.1 0).val, v.2 0, v.2 1;
    sigma n (v.2 0), (v.1 1).val, v.2 2;
    sigma n (v.2 1), sigma n (v.2 2), (v.1 2).val], by
    have hs : ∀ x, sigma n (sigma n x) = x := sigma_involutive n
    have hf (c : F n) : sigma n c.val = c.val := c.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoint, hs, hf]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entry_conjugate]
  right_inv v := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl
  map_smul' c X := by
    apply Prod.ext
    · rfl
    · ext i; fin_cases i <;> rfl

theorem finrank_space : Module.finrank (F n) (Space n) = 9 := by
  rw [(coordinates n).finrank_eq, Module.finrank_prod]
  simp [Module.finrank_pi_fintype, finrank_E]

/-- The literal linear-equivalence-valued descended action. -/
def actionHom : Cover n →* (Space n ≃ₗ[F n] Space n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (F n) (Space n)).toMonoidHom.comp
    (action n).asGroupHom

def actionImage : Subgroup (Space n ≃ₗ[F n] Space n) := (actionHom n).range

abbrev Image := actionImage n

/-- The quotient map to the actual faithful image. -/
def toImage : Cover n →* Image n := (actionHom n).rangeRestrict

def imageAction : Representation (F n) (Image n) (Space n) where
  toFun g := g.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

theorem imageAction_faithful : Function.Injective (imageAction n) := by
  intro g h he
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective he

theorem imageAction_toImage (g : Cover n) (X : Space n) :
    imageAction n (toImage n g) X = action n g X := rfl

/-- Prime-field scalars on the fixed coefficient field. -/
instance fixedBinaryAlgebra : Algebra (ZMod 2) (F n) := ZMod.algebra (F n) 2

/-- Restrict the descended module to the binary prime field. -/
instance binaryModule : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (F n))

def binaryAction : Representation (ZMod 2) (Cover n) (Space n) where
  toFun g := (action n g).toAddMonoidHom.toZModLinearMap 2
  map_one' := by apply LinearMap.ext; intro X; exact congrArg (fun f => f X) (action n).map_one
  map_mul' g h := by apply LinearMap.ext; intro X; exact congrArg (fun f => f X) ((action n).map_mul g h)

theorem binaryAction_apply (g : Cover n) (X : Space n) :
    binaryAction n g X = action n g X := rfl

theorem finrank_binary : Module.finrank (ZMod 2) (Space n) = 9 * n := by
  have hF := Module.natCard_eq_pow_finrank (K := F n) (V := Space n)
  rw [card_F, finrank_space, ← pow_mul] at hF
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space n)
  have hc : Nat.card (ZMod 2) = 2 := by simp
  rw [hc, hF] at h2
  have hh : n * 9 = Module.finrank (ZMod 2) (Space n) :=
    (pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2
  omega

end Representation.HermitianTensorThree
