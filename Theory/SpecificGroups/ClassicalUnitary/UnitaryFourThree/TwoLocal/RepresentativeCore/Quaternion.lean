module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.StandardInvolution
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.FinCases

/-!
# The concrete quaternion central product in the PSU₄(3) involution centralizer

Over the field of nine elements, the matrices diag(i,-i) and
[[0,1],[-1,0]] generate a copy of Q₈. Two such copies act on the two
coordinate planes. Their block-diagonal product lies in SU₄ and commutes
with diag(-1,-1,1,1), so projection gives a subgroup of the actual
projective involution centralizer.

The restricted projective kernel consists precisely of the two diagonal
signs. Thus the image is the central product Q₈ * Q₈ of order 32, and is a
two-group. This computes the intersection with the full scalar kernel;
it does not replace the full order-four scalar kernel by a sign quotient.
Normality in the full projective centralizer, its centralizer, and the
quotient two-core are separate obligations in the parent calculation.

Sources: the concrete quaternion representation, and the SU/PSU conventions
in GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`). The application is
Aschbacher–Smith, Theorem 0.1.2(4) and condition E, printed pp.3–4 of
`refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) FiniteField.Nine
abbrev Mat₄ := Matrix (Fin 4) (Fin 4) FiniteField.Nine

/-- The chosen square root of minus one in the concrete quadratic field. -/
def imaginary : FiniteField.Nine := ⟨0, 1⟩
def quaternionI : Mat₂ := !![imaginary, 0; 0, -imaginary]
def quaternionJ : Mat₂ := !![0, 1; -1, 0]
/-- The standard two-dimensional quaternion representation. -/
def quaternionMatrix : QuaternionGroup 2 → Mat₂
  | .a k => quaternionI ^ k.val
  | .xa k => quaternionJ * quaternionI ^ k.val

def quaternionMatrixHom : QuaternionGroup 2 →* Mat₂ where
  toFun := quaternionMatrix
  map_one' := by decide
  map_mul' := by
    exact (by decide +kernel : ∀ x y, quaternionMatrix (x * y) =
      quaternionMatrix x * quaternionMatrix y)

theorem quaternionMatrix_unitary (q : QuaternionGroup 2) :
    (quaternionMatrix q).conjTranspose * quaternionMatrix q = 1 := by
  rcases q with i | i <;> fin_cases i <;> decide

theorem quaternionMatrix_det (q : QuaternionGroup 2) : (quaternionMatrix q).det = 1 := by
  rcases q with i | i <;> fin_cases i <;> decide

/-- The two coordinate planes, in the same order as the standard involution. -/
def block (A B : Mat₂) : Mat₄ :=
  !![A 0 0, A 0 1, 0, 0;
     A 1 0, A 1 1, 0, 0;
     0, 0, B 0 0, B 0 1;
     0, 0, B 1 0, B 1 1]

theorem block_one : block 1 1 = 1 := by decide

theorem block_mul (A B C D : Mat₂) : block A B * block C D = block (A * C) (B * D) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_succ]

theorem block_adj (A B : Mat₂) : (block A B).conjTranspose = block A.conjTranspose B.conjTranspose := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.conjTranspose_apply]

theorem block_det (A B : Mat₂) : (block A B).det = A.det * B.det := by
  have h : block A B = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def quaternionPairMatrixHom : (QuaternionGroup 2 × QuaternionGroup 2) →* Mat₄ where
  toFun q := block (quaternionMatrix q.1) (quaternionMatrix q.2)
  map_one' := by
    change block (quaternionMatrixHom 1) (quaternionMatrixHom 1) = 1
    rw [map_one, block_one]
  map_mul' x y := by
    change block (quaternionMatrixHom (x.1 * y.1)) (quaternionMatrixHom (x.2 * y.2)) = _
    rw [map_mul, map_mul]
    exact (block_mul _ _ _ _).symm

theorem block_commutes_standard (A B : Mat₂) :
    block A B * standardInvolutionMatrix = standardInvolutionMatrix * block A B := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [block, standardInvolutionMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The literal block-diagonal quaternion product in SU₄. -/
noncomputable def quaternionPairSU : (QuaternionGroup 2 × QuaternionGroup 2) →*
    (form 4).specialSubgroup :=
  quaternionPairMatrixHom.toHomUnits.codRestrict _ (by
    intro q
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (block (quaternionMatrix q.1) (quaternionMatrix q.2)).conjTranspose * 1 *
        block (quaternionMatrix q.1) (quaternionMatrix q.2) = 1
      rw [mul_one, block_adj, block_mul, quaternionMatrix_unitary, quaternionMatrix_unitary,
        block_one]
    · apply Units.ext
      change (block (quaternionMatrix q.1) (quaternionMatrix q.2)).det = 1
      rw [block_det, quaternionMatrix_det, quaternionMatrix_det, one_mul])

theorem quaternionPairSU_val (q : QuaternionGroup 2 × QuaternionGroup 2) :
    (quaternionPairSU q).val.val = block (quaternionMatrix q.1) (quaternionMatrix q.2) := rfl

/-- Projection into the full centralizer, retaining its actual ambient type. -/
noncomputable def quaternionPair : (QuaternionGroup 2 × QuaternionGroup 2) →* standardCentralizer :=
  ((project 4).comp quaternionPairSU).codRestrict _ (by
    intro q
    exact (project_mem_standardCentralizer_iff _).mpr
      (Or.inl (block_commutes_standard _ _)))

/-- The candidate intrinsic two-core; its normality is not assumed here. -/
noncomputable def quaternionCore : Subgroup standardCentralizer := quaternionPair.range

theorem quaternionCore_isPGroup : IsPGroup 2 quaternionCore := by
  have hp : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 6)
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact hp.of_surjective quaternionPair.rangeRestrict quaternionPair.rangeRestrict_surjective

theorem quaternionPair_mem (q : QuaternionGroup 2 × QuaternionGroup 2) :
    quaternionPair q ∈ quaternionCore := ⟨q, rfl⟩

private theorem quaternionMatrix_scalar (q : QuaternionGroup 2) (u : FiniteField.Nine)
    (h : quaternionMatrix q = Matrix.scalar (Fin 2) u) :
    (q = 1 ∧ u = 1) ∨ (q = .a 2 ∧ u = -1) := by
  exact (by decide +kernel : ∀ (q : QuaternionGroup 2) (u : FiniteField.Nine),
    quaternionMatrix q = Matrix.scalar (Fin 2) u →
      (q = 1 ∧ u = 1) ∨ (q = .a 2 ∧ u = -1)) q u h

private theorem quaternionPair_scalar (q : QuaternionGroup 2 × QuaternionGroup 2)
    (u : FiniteField.Nine)
    (h : block (quaternionMatrix q.1) (quaternionMatrix q.2) = Matrix.scalar (Fin 4) u) :
    q = 1 ∨ q = (.a 2, .a 2) := by
  have h₁ : quaternionMatrix q.1 = Matrix.scalar (Fin 2) u := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M : Mat₄ => M (Fin.castAdd 2 i) (Fin.castAdd 2 j)) h
    fin_cases i <;> fin_cases j <;> exact he
  have h₂ : quaternionMatrix q.2 = Matrix.scalar (Fin 2) u := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M : Mat₄ => M (Fin.natAdd 2 i) (Fin.natAdd 2 j)) h
    fin_cases i <;> fin_cases j <;> exact he
  have hne : (1 : FiniteField.Nine) ≠ -1 := by decide
  rcases quaternionMatrix_scalar q.1 u h₁ with ⟨h₁, hu₁⟩ | ⟨h₁, hu₁⟩ <;>
    rcases quaternionMatrix_scalar q.2 u h₂ with ⟨h₂, hu₂⟩ | ⟨h₂, hu₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact (hne (hu₁.symm.trans hu₂)).elim
  · exact (hne (hu₂.symm.trans hu₁)).elim
  · exact Or.inr (Prod.ext h₁ h₂)

/-- Precisely the diagonal signs disappear in the projective image. -/
theorem quaternionPair_eq_one_iff (q : QuaternionGroup 2 × QuaternionGroup 2) :
    quaternionPair q = 1 ↔ q = 1 ∨ q = (.a 2, .a 2) := by
  constructor
  · intro h
    have he : ProjGenLinGroup.mk (quaternionPairSU q).val = 1 :=
      congrArg (fun g : standardCentralizer => g.val.val) h
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he
    obtain ⟨u, hu⟩ := he
    exact quaternionPair_scalar q u.val (congrArg Units.val hu).symm
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext
      apply Subtype.ext
      change ProjGenLinGroup.mk (quaternionPairSU (.a 2, .a 2)).val = 1
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨-1, ?_⟩
      apply Units.ext
      change Matrix.scalar (Fin 4) (-1 : FiniteField.Nine) =
        block (quaternionMatrix (.a 2)) (quaternionMatrix (.a 2))
      decide

theorem quaternionPair_kernel_card : Nat.card quaternionPair.ker = 2 := by
  have e : quaternionPair.ker ≃
      {q : QuaternionGroup 2 × QuaternionGroup 2 // q = 1 ∨ q = (.a 2, .a 2)} :=
    Equiv.subtypeEquivRight quaternionPair_eq_one_iff
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

/-- The order follows from the explicit kernel, without ambient order recognition. -/
theorem quaternionCore_card : Nat.card quaternionCore = 32 := by
  have h := quaternionPair.ker.card_mul_index
  rw [Subgroup.index_ker, quaternionPair_kernel_card] at h
  have hc : Nat.card (QuaternionGroup 2 × QuaternionGroup 2) = 64 := by
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  change 2 * Nat.card quaternionCore = _ at h
  omega

/-- The chosen involution viewed as an element of its own centralizer. -/
def centralInvolution : standardCentralizer :=
  ⟨standardInvolution, by rw [Subgroup.mem_centralizer_singleton_iff]⟩

theorem quaternionPair_sign_left : quaternionPair (.a 2, 1) = centralInvolution := by
  apply Subtype.ext
  change project 4 (quaternionPairSU (.a 2, 1)) = project 4 standardInvolutionSU
  congr 1
  apply Subtype.ext
  apply Units.ext
  change block (quaternionMatrix (.a 2)) (quaternionMatrix 1) = standardInvolutionMatrix
  decide

theorem centralInvolution_mem_quaternionCore : centralInvolution ∈ quaternionCore := by
  rw [← quaternionPair_sign_left]
  exact quaternionPair_mem _

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
