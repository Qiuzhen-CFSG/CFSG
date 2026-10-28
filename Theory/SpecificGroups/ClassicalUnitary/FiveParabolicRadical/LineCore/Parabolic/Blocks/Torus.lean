module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# The cubic torus in the unitary-five line parabolic

In the Witt basis, a cubic root `b` gives the matrix `diag(b²,1,1,1,b)`.
It is special unitary, commutes with the middle SU₃, and acts on the radical
coordinates by `(v,t) ↦ (b²v,bt)`. Conjugating by the supplied trace-one Witt
basis realizes this torus in the actual projective flag stabilizer.

Source: the classical parabolic calculation supporting Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable {F : Type*} [Field F]

abbrev Cubic := rootsOfUnity 3 F

@[simp] theorem cubic_pow (b : Cubic (F := F)) : (b.val : F) ^ 3 = 1 :=
  (mem_rootsOfUnity' 3 b.val).mp b.property

@[simp] theorem cubic_pow_four (b : Cubic (F := F)) : (b.val : F) ^ 4 = b.val := by
  rw [show 4 = 3 + 1 from rfl, pow_succ, cubic_pow, one_mul]

theorem cubic_card [Finite F] (hcard : Nat.card F = 16) :
    Nat.card (Cubic (F := F)) = 3 := by
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  decide

def cubicDiagonal (b : Cubic (F := F)) : Matrix (Fin 5) (Fin 5) F :=
  diagonal ![(b.val : F) ^ 2, 1, 1, 1, (b.val : F)]

@[simp] theorem cubicDiagonal_one : cubicDiagonal (1 : Cubic (F := F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicDiagonal]

theorem cubicDiagonal_mul (b d : Cubic (F := F)) :
    cubicDiagonal (b * d) = cubicDiagonal b * cubicDiagonal d := by
  simp only [cubicDiagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_pow]

theorem cubicDiagonal_det (b : Cubic (F := F)) : (cubicDiagonal b).det = 1 := by
  simp [cubicDiagonal, det_diagonal, Fin.prod_univ_succ, ← pow_succ]

def cubicDiagonalGL : Cubic (F := F) →* GL (Fin 5) F where
  toFun b := ⟨cubicDiagonal b, cubicDiagonal b⁻¹,
    by rw [← cubicDiagonal_mul, mul_inv_cancel, cubicDiagonal_one],
    by rw [← cubicDiagonal_mul, inv_mul_cancel, cubicDiagonal_one]⟩
  map_one' := Units.ext cubicDiagonal_one
  map_mul' b d := Units.ext (cubicDiagonal_mul b d)

variable (J : HermitianForm 5 F) (hconj : ∀ x, J.conj x = x ^ 4)

include hconj in
@[simp] theorem conj_cubic (b : Cubic (F := F)) : J.conj (b.val : F) = b.val := by
  rw [hconj, cubic_pow_four]

include hconj in
theorem cubicDiagonal_preserves (b : Cubic (F := F)) :
    J.conjTranspose (cubicDiagonal b) * wittGram * cubicDiagonal b = wittGram := by
  have hb := cubic_pow b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicDiagonal, wittGram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, conj_cubic J hconj,
      ← pow_succ, ← pow_succ']

include hconj in
theorem pairing_cubic (b : Cubic (F := F)) (v w : Fin 3 → F) :
    pairing J (fun i => (b.val : F) ^ 2 * v i) (fun i => (b.val : F) ^ 2 * w i) =
      (b.val : F) * pairing J v w := by
  simp only [pairing, map_mul, map_pow, conj_cubic J hconj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (b.val : F) ^ 2 * J.conj (v i) * ((b.val : F) ^ 2 * w i) =
        (b.val : F) ^ 4 * (J.conj (v i) * w i) := by ring
    _ = _ := by rw [cubic_pow_four]

def cubicScale (b : Cubic (F := F)) (u : Coord J) : Coord J where
  vector i := (b.val : F) ^ 2 * u.vector i
  scalar := (b.val : F) * u.scalar
  trace_eq := by
    rw [map_mul, conj_cubic J hconj, ← mul_add, u.trace_eq]
    exact (pairing_cubic J hconj b u.vector u.vector).symm

@[simp] theorem cubicScale_vector (b : Cubic (F := F)) (u : Coord J) (i : Fin 3) :
    (cubicScale J hconj b u).vector i = (b.val : F) ^ 2 * u.vector i := rfl
@[simp] theorem cubicScale_scalar (b : Cubic (F := F)) (u : Coord J) :
    (cubicScale J hconj b u).scalar = (b.val : F) * u.scalar := rfl

@[simp] theorem cubicScale_one (u : Coord J) : cubicScale J hconj 1 u = u := by
  apply Coord.ext
  · ext i; simp
  · simp

theorem cubicScale_mul (b d : Cubic (F := F)) (u : Coord J) :
    cubicScale J hconj (b * d) u = cubicScale J hconj b (cubicScale J hconj d u) := by
  apply Coord.ext
  · ext i; simp [mul_pow, mul_assoc]
  · simp [mul_assoc]

variable [CharP F 2]

def cubicAction : Cubic (F := F) →* MulAut (Coord J) where
  toFun b :=
    { toFun := cubicScale J hconj b
      invFun := cubicScale J hconj b⁻¹
      left_inv u := by rw [← cubicScale_mul, inv_mul_cancel, cubicScale_one]
      right_inv u := by rw [← cubicScale_mul, mul_inv_cancel, cubicScale_one]
      map_mul' u v := by
        apply Coord.ext
        · ext i; simp [mul_add]
        · simp only [cubicScale_scalar, Coord.mul_scalar]
          change (b.val : F) * (u.scalar + v.scalar + pairing J u.vector v.vector) =
            (b.val : F) * u.scalar + (b.val : F) * v.scalar +
              pairing J (fun i => (b.val : F) ^ 2 * u.vector i)
                (fun i => (b.val : F) ^ 2 * v.vector i)
          rw [pairing_cubic J hconj]
          ring }
  map_one' := MulEquiv.ext (cubicScale_one J hconj)
  map_mul' b d := MulEquiv.ext (cubicScale_mul J hconj b d)

omit [CharP F 2] in
@[simp] theorem cubicAction_apply (b : Cubic (F := F)) (u : Coord J) :
    cubicAction J hconj b u = cubicScale J hconj b u := rfl

omit [CharP F 2] in
/-- Matrix verification of the action on both radical coordinates. -/
theorem cubicDiagonal_commutation (b : Cubic (F := F)) (u : Coord J) :
    unipotentMatrix J (cubicScale J hconj b u) * cubicDiagonal b =
      cubicDiagonal b * unipotentMatrix J u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentMatrix, cubicDiagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul, conj_cubic J hconj] <;>
    ring_nf <;> simp

/-- Conjugation by the supplied Witt basis. -/
def cubicGL (c : F) : Cubic (F := F) →* GL (Fin 5) F :=
  (MulAut.conj (wittBasisGL c)).toMonoidHom.comp cubicDiagonalGL

@[simp] theorem cubicGL_val (c : F) (b : Cubic (F := F)) :
    (cubicGL c b).val = wittBasisMatrix c * cubicDiagonal b * wittBasisInverse c := rfl

def cubicAmbientMatrix (c : F) (b : Cubic (F := F)) : Matrix (Fin 5) (Fin 5) F :=
  !![(b.val : F)^2 * (1+c) + c * (b.val : F), (b.val : F)^2 * c + c * (b.val : F),0,0,0;
     (b.val : F)^2 * (1+c) + (1+c) * (b.val : F),
       (b.val : F)^2 * c + (1+c) * (b.val : F),0,0,0;
     0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1]

theorem cubicGL_matrix (c : F) (b : Cubic (F := F)) :
    (cubicGL c b).val = cubicAmbientMatrix c b := by
  rw [cubicGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittBasisMatrix, wittBasisInverse, cubicDiagonal, cubicAmbientMatrix,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

omit [CharP F 2] in
private theorem adjoint_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((A * B).map J.conj).transpose = _
  rw [Matrix.map_mul, Matrix.transpose_mul]
  rfl

/-- Transport a Witt-form isometry into the stored identity-form group. -/
theorem witt_conjugate_preserves (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (D : Matrix (Fin 5) (Fin 5) F)
    (hD : J.conjTranspose D * wittGram * D = wittGram) :
    J.conjTranspose (wittBasisMatrix c * D * wittBasisInverse c) * J.form *
      (wittBasisMatrix c * D * wittBasisInverse c) = J.form := by
  let B := wittBasisMatrix c
  let I := wittBasisInverse c
  have hBI : B * I = 1 := wittBasis_mul_inverse c
  have hgram : J.conjTranspose B * J.form * B = wittGram :=
    wittBasis_gram J c hc hJ
  have hback : J.conjTranspose I * wittGram * I = J.form := by
    rw [← hgram]
    calc
      J.conjTranspose I * (J.conjTranspose B * J.form * B) * I =
          J.conjTranspose (B * I) * J.form * (B * I) := by
        rw [adjoint_mul]; simp only [mul_assoc]
      _ = J.form := by
        rw [hBI]
        have h1 : J.conjTranspose 1 = 1 := by
          ext i j
          by_cases h : i = j <;> simp [HermitianForm.conjTranspose, Matrix.one_apply, h, Ne.symm]
        rw [h1, one_mul, mul_one]
  change J.conjTranspose (B * D * I) * J.form * (B * D * I) = J.form
  rw [adjoint_mul, adjoint_mul]
  calc
    J.conjTranspose I * (J.conjTranspose D * J.conjTranspose B) * J.form * (B * D * I) =
        J.conjTranspose I * (J.conjTranspose D *
          (J.conjTranspose B * J.form * B) * D) * I := by simp only [mul_assoc]
    _ = J.form := by rw [hgram, hD, hback]

set_option maxRecDepth 2048 in
def cubicSU (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Cubic (F := F) →* J.specialSubgroup :=
  (cubicGL c).codRestrict _ (by
    intro b
    rw [J.mem_specialSubgroup_iff]
    constructor
    · exact witt_conjugate_preserves J c hc hJ _ (cubicDiagonal_preserves J hconj b)
    · have hd : GeneralLinearGroup.det (cubicDiagonalGL b) = 1 :=
        Units.ext (cubicDiagonal_det b)
      change GeneralLinearGroup.det
        (wittBasisGL c * cubicDiagonalGL b * (wittBasisGL c)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hd, mul_one, mul_inv_cancel])

/-- Multiplication in the actual basis agrees with the diagonal Witt action. -/
theorem cubicGL_mul_basis (c : F) (b : Cubic (F := F)) (v : Fin 5 → F) :
    (cubicGL c b).val *ᵥ (wittBasisMatrix c *ᵥ v) =
      wittBasisMatrix c *ᵥ (cubicDiagonal b *ᵥ v) := by
  rw [cubicGL_val, mulVec_mulVec, mul_assoc, wittBasis_inverse_mul, mul_one,
    mulVec_mulVec]

theorem cubicSU_mem_line (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (b : Cubic (F := F)) : cubicSU J hconj c hc hJ b ∈ specialStabilizer J (line F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  have h (w : Fin 5 → F) :
      (cubicGL c b).val *ᵥ (wittBasisMatrix c *ᵥ w) ∈ line F ↔
        wittBasisMatrix c *ᵥ w ∈ line F := by
    rw [cubicGL_mul_basis, wittBasis_mem_line_iff, wittBasis_mem_line_iff]
    simp [cubicDiagonal, mulVec_diagonal]
  have he : wittBasisMatrix c *ᵥ (wittBasisInverse c *ᵥ v) = v := by
    rw [mulVec_mulVec, wittBasis_mul_inverse, one_mulVec]
  change (cubicGL c b).val *ᵥ v ∈ _ ↔ v ∈ _
  simpa only [he] using h (wittBasisInverse c *ᵥ v)

theorem cubicSU_mem_plane (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (b : Cubic (F := F)) : cubicSU J hconj c hc hJ b ∈ specialStabilizer J (plane F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  have h (w : Fin 5 → F) :
      (cubicGL c b).val *ᵥ (wittBasisMatrix c *ᵥ w) ∈ plane F ↔
        wittBasisMatrix c *ᵥ w ∈ plane F := by
    rw [cubicGL_mul_basis, wittBasis_mem_plane_iff, wittBasis_mem_plane_iff]
    simp [cubicDiagonal, mulVec_diagonal]
  have he : wittBasisMatrix c *ᵥ (wittBasisInverse c *ᵥ v) = v := by
    rw [mulVec_mulVec, wittBasis_mul_inverse, one_mulVec]
  change (cubicGL c b).val *ᵥ v ∈ _ ↔ v ∈ _
  simpa only [he] using h (wittBasisInverse c *ᵥ v)

/-- The cubic torus inside the actual projective line parabolic. -/
def cubicParabolic (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Cubic (F := F) →* lineParabolic J :=
  ((project J).comp (cubicSU J hconj c hc hJ)).codRestrict _ (fun b =>
    ⟨cubicSU J hconj c hc hJ b, cubicSU_mem_line J hconj c hc hJ b, rfl⟩)

theorem cubicParabolic_mem_overlap (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (b : Cubic (F := F)) :
    cubicParabolic J hconj c hc hJ b ∈
      (lineParabolic J ⊓ planeParabolic J).subgroupOf (lineParabolic J) :=
  ⟨(cubicParabolic J hconj c hc hJ b).property,
    ⟨cubicSU J hconj c hc hJ b, cubicSU_mem_plane J hconj c hc hJ b, rfl⟩⟩

/-- The coordinate automorphism is conjugation by the actual torus matrices. -/
theorem toParabolic_cubicAction (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (b : Cubic (F := F)) (u : Coord J) :
    toParabolic J hJ (cubicAction J hconj b u) =
      cubicParabolic J hconj c hc hJ b * toParabolic J hJ u *
        (cubicParabolic J hconj c hc hJ b)⁻¹ := by
  have hd : unipotentGL J (cubicAction J hconj b u) * cubicDiagonalGL b =
      cubicDiagonalGL b * unipotentGL J u := Units.ext (cubicDiagonal_commutation J hconj b u)
  have hs : toSU J hJ (cubicAction J hconj b u) * cubicSU J hconj c hc hJ b =
      cubicSU J hconj c hc hJ b * toSU J hJ u := by
    apply Subtype.ext
    change ambientGL J _ * (wittBasisGL c * cubicDiagonalGL b * (wittBasisGL c)⁻¹) =
      (wittBasisGL c * cubicDiagonalGL b * (wittBasisGL c)⁻¹) * ambientGL J u
    rw [ambientGL_eq J c, ambientGL_eq J c]
    have hh := congrArg (fun X : GL (Fin 5) F => wittBasisGL c * X * (wittBasisGL c)⁻¹) hd
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  have he := (eq_mul_inv_iff_mul_eq).mpr hs
  apply Subtype.ext
  exact (congrArg (project J) he).trans (by simp only [map_mul, map_inv]; rfl)

/-- The middle SU₃ commutes with the torus already before projectivization. -/
theorem cubicSU_commute_levi (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (b : Cubic (F := F)) (A : (middleForm J).specialSubgroup) :
    Commute (cubicSU J hconj c hc hJ b) (leviSU J hJ A) := by
  apply Subtype.ext
  apply Units.ext
  change (cubicGL c b).val * leviMatrix A.val.val =
    leviMatrix A.val.val * (cubicGL c b).val
  rw [cubicGL_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicAmbientMatrix, leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cubicParabolic_commute_levi (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (b : Cubic (F := F)) (A : (middleForm J).specialSubgroup) :
    Commute (cubicParabolic J hconj c hc hJ b) (leviParabolic J hJ A) := by
  apply Subtype.ext
  exact (project J).map_mul _ _ |>.symm.trans
    ((congrArg (project J) (cubicSU_commute_levi J hconj c hc hJ b A)).trans
      ((project J).map_mul _ _))

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
