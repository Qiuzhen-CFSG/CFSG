module
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

namespace BSConverse

universe u v w

/-! ## 1. Strong embedding -/

/-- An involution: a nonidentity element of order dividing two. -/
@[expose] public def IsInvolution {G : Type*} [Group G] (x : G) : Prop := x ≠ 1 ∧ x ^ 2 = 1

/-- `M` is **strongly embedded** in `X`: proper, containing an involution, and meeting each
of its other conjugates in a subgroup containing none.

Conjugation is `M ↦ g M g⁻¹`; `M.map (MulAut.conj g).toMonoidHom` is Mathlib's spelling of
that.  Because `g` ranges over all of `G ∖ M` and `g ∉ M ↔ g⁻¹ ∉ M`, conjugating on the
other side gives the same notion.

This is `IsStronglyEmbedded` as `BenderSuzuki/FinalTheorem.lean` states it, word for
word. -/
@[expose] public def IsStronglyEmbedded {X : Type*} [Group X] (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧ (∃ x ∈ M, IsInvolution x) ∧
    ∀ g ∉ M, ∀ x ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom, ¬ IsInvolution x

/-! ## 2. Hypothesis (A) -/

/-- `H^g = g⁻¹ H g`, Peterfalvi's exponent convention -- the opposite side from
`IsStronglyEmbedded` above, which is why the two are stated differently. -/
@[expose] public def rightConjugate {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

/-- The 2-rank of `G` is at least two: `G` has a Klein four subgroup. -/
@[expose] public def TwoRankAtLeastTwo (G : Type*) [Group G] : Prop :=
  ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x : E, (x : E) ^ 2 = 1

/-- **Hypothesis (A1)**, Peterfalvi Part II.  `G` acts doubly transitively on `Ω`, `H` is a
point stabiliser, `t` is an involution outside `H`, `D = H ∩ H^t`, and `H = Q ⋊ D` with
`|Q|` even and `|D|` odd.  The semidirect product is spelled out as five separate fields
rather than as `IsComplement'`. -/
public structure HypothesisA1 (G Ω : Type*) [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) : Prop where
  two_transitive : MulAction.IsMultiplyPretransitive G Ω 2
  point_stabilizer : ∃ point : Ω, H = MulAction.stabilizer G point
  involution_t : IsInvolution t
  t_not_mem_H : t ∉ H
  D_eq : D = H ⊓ rightConjugate H t
  Q_le_H : Q ≤ H
  D_le_H : D ≤ H
  Q_normal_in_H : (Q.subgroupOf H).Normal
  Q_disjoint_D : Disjoint Q D
  Q_sup_D : Q ⊔ D = H
  Q_even : Even (Nat.card (↥Q))
  D_odd : Odd (Nat.card (↥D))

/-- **Hypothesis (A)**: (A1) together with (A2) faithfulness and (A3) 2-rank at least two.

(A3) is not decoration.  Without it, strong embedding does not pin down the group: the
normaliser of a cyclic or generalised quaternion Sylow 2-subgroup is strongly embedded
too.  Both halves are needed for the reading given at the top of this file. -/
public structure HypothesisA (G Ω : Type*) [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) : Prop where
  A1 : HypothesisA1 G Ω H D Q t
  A2 : FaithfulSMul G Ω
  A3 : TwoRankAtLeastTwo G

/-! ## 3. The three groups

Each is defined from Mathlib primitives alone. -/

/-- The field of order `2ᵐ`. -/
public abbrev BinaryGaloisField (m : ℕ) : Type := GaloisField 2 m

/-- `PSL(2, 2ᵏ)`. -/
public abbrev PSL2Model (m : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (BinaryGaloisField m)

/-- A nondegenerate Hermitian form on `Fⁿ`, carrying its field involution. -/
public structure HermitianForm (n : ℕ) (F : Type w) [Field F] where
  conj : F ≃+* F
  conj_involutive : Function.Involutive conj
  form : Matrix (Fin n) (Fin n) F
  form_hermitian : ∀ i j, conj (form j i) = form i j
  form_nondegenerate : form.det ≠ 0

/-- Conjugate transpose with respect to the stored involution. -/
@[expose] public def HermitianForm.conjTranspose {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  fun i j => J.conj (A j i)

/-- The adjoint is antimultiplicative. -/
public theorem HermitianForm.adj_mul {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F)
    (A B : Matrix (Fin n) (Fin n) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  ext i j
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, map_sum, map_mul, mul_comm]

/-- The adjoint fixes the identity. -/
public theorem HermitianForm.adj_one {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F) :
    J.conjTranspose (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, h, h.symm]

/-- The adjoint of an inverse undoes the adjoint. -/
public theorem HermitianForm.adj_inv {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F)
    (A : GL (Fin n) F) :
    J.conjTranspose ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * J.conjTranspose A = 1 := by
  rw [← adj_mul]
  simp [adj_one]

/-- The isometry group of `J`.  The carrier is `{A | Aᴴ J A = J}`; the three fields below
it are the routine proof that that set is a subgroup. -/
@[expose] public def HermitianForm.unitarySubgroup {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) : Subgroup (GL (Fin n) F) where
  carrier := {A | J.conjTranspose (A : Matrix (Fin n) (Fin n) F) * J.form * A = J.form}
  one_mem' := by simp [HermitianForm.adj_one]
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.coe_mul, HermitianForm.adj_mul] at *
    calc J.conjTranspose (B : Matrix (Fin n) (Fin n) F) * J.conjTranspose A * J.form * (A * B)
        = J.conjTranspose (B : Matrix (Fin n) (Fin n) F) *
            (J.conjTranspose A * J.form * A) * B := by simp only [mul_assoc]
      _ = J.form := by rw [hA, hB]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    calc J.conjTranspose ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * J.form * A⁻¹
        = J.conjTranspose ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (J.conjTranspose A * J.form * A) * A⁻¹ := by rw [hA]
      _ = (J.conjTranspose ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            J.conjTranspose A) * J.form * ((A : Matrix (Fin n) (Fin n) F) * A⁻¹) := by
          simp only [mul_assoc]
      _ = J.form := by rw [HermitianForm.adj_inv]; simp

/-- Isometries of determinant one. -/
@[expose] public def HermitianForm.specialSubgroup {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) : Subgroup (GL (Fin n) F) :=
  J.unitarySubgroup ⊓ Matrix.GeneralLinearGroup.det.ker

/-- `PSU(J)`, the image of `SU(J)` in `PGL`. -/
public abbrev PSUModel {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F) :=
  J.specialSubgroup.map Matrix.ProjGenLinGroup.mk

/-- The Suzuki root matrix over `GF(2^(2m+1))`; the Tits exponent is `2^(m+1)`. -/
@[expose] public noncomputable def SzRootMatrix (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![1, a, b, a ^ (2 + 2 ^ (m + 1)) + a * b + b ^ (2 ^ (m + 1));
     0, 1, a ^ (2 ^ (m + 1)), a ^ (1 + 2 ^ (m + 1)) + b;
     0, 0, 1, a;
     0, 0, 0, 1]

/-- The Suzuki torus matrix `diag(x^(1+2^m), x^(2^m), x^(-2^m), x^(-1-2^m))`. -/
@[expose] public noncomputable def SzTorusMatrix (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m)), 0, 0, 0;
     0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m)), 0, 0;
     0, 0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m))⁻¹, 0;
     0, 0, 0, ((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m))⁻¹]

/-- The Suzuki Weyl matrix: the antidiagonal permutation. -/
@[expose] public noncomputable def SzWeylMatrix (m : ℕ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- The root matrix as an element of `GL(4, GF(2^(2m+1)))`; the proof is the determinant
computation. -/
@[expose] public noncomputable def SzRootGL (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SzRootMatrix m a b) (by
    classical
    have htri : (SzRootMatrix m a b).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SzRootMatrix] at hij ⊢
    rw [Matrix.det_of_upperTriangular htri]
    simp [SzRootMatrix, Fin.prod_univ_four])

/-- The torus matrix as an element of `GL(4, GF(2^(2m+1)))`. -/
@[expose] public noncomputable def SzTorusGL (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SzTorusMatrix m x) (by
    classical
    have htri : (SzTorusMatrix m x).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SzTorusMatrix] at hij ⊢
    rw [Matrix.det_of_upperTriangular htri]
    have hx_sigma : (x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    have hx_outer : (x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    simp [SzTorusMatrix, Fin.prod_univ_four, hx_sigma, hx_outer])

/-- The Weyl matrix as an element of `GL(4, GF(2^(2m+1)))`; it is its own inverse. -/
@[expose] public noncomputable def SzWeylGL (m : ℕ) : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  { val := SzWeylMatrix m
    inv := SzWeylMatrix m
    val_inv := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SzWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SzWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] }

/-- The generators of `Sz(2^(2m+1))`: root elements, torus elements, and the Weyl
element. -/
@[expose] public def SzGeneratorSet (m : ℕ) : Set (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  {A | (∃ a b, A = SzRootGL m a b) ∨ (∃ x, A = SzTorusGL m x) ∨ A = SzWeylGL m}

/-- `Sz(2^(2m+1))` in its concrete matrix model. -/
@[expose] public noncomputable def SzModel (m : ℕ) : Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  Subgroup.closure (SzGeneratorSet m)

end BSConverse
