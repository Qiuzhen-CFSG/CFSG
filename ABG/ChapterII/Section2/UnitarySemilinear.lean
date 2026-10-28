module
public import ABG.ChapterII.Section2.UnitaryDeterminantModels
public import Theory.SpecificGroups.GL2.Semilinear

/-!
# The actual semilinear unitary group

The full coefficient automorphism group of `GF(p^(2n))` acts entrywise on
the existing standard GU2. Its semidirect product is `GammaU2`; every
determinant level has normal image in that group. This is the unitary
semilinear model used in ABG Chapter II, Section 3, Proposition 3, article
pages 24-27. The coefficient group acts on the quadratic field, not just
on its subfield of order `p^n`.

Every field automorphism commutes with the q-power Frobenius by preservation
of powers. Mapping the defining Hermitian equation therefore preserves
unitarity, since the Gram matrix is the identity. Restricting the actual
GL2 coefficient equivalences gives the unitary action. Determinant-level
invariance follows from the GL2 determinant map criterion; semidirect
conjugation then combines coefficient invariance with inner normality.
The exact original GU2 instances are retained, and no abstract action,
special-unitary/special-linear identification, or recognition is assumed.
-/

namespace ABG

open Matrix.GeneralLinearGroup

private theorem coefficientMap_mem_GU2
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (e : GaloisField p (2 * n) ≃+* GaloisField p (2 * n))
    (A : GL (Fin 2) (GaloisField p (2 * n)))
    (hA : A ∈ (unitaryForm 2 p n hn).unitarySubgroup) :
    coefficientEquiv e A ∈ (unitaryForm 2 p n hn).unitarySubgroup := by
  rw [(unitaryForm 2 p n hn).mem_unitarySubgroup_iff] at hA ⊢
  let J := unitaryForm 2 p n hn
  have hct : J.conjTranspose ((coefficientEquiv e A).val) =
      e.mapMatrix (J.conjTranspose A.val) := by
    ext i j
    change (e (A j i)) ^ (p ^ n) = e ((A j i) ^ (p ^ n))
    exact (map_pow e (A j i) (p ^ n)).symm
  change J.conjTranspose (coefficientEquiv e A).val * 1 * (coefficientEquiv e A).val = 1
  rw [hct]
  change J.conjTranspose A.val * 1 * A.val = 1 at hA
  have h := congrArg e.mapMatrix hA
  rw [map_mul, map_mul, map_one, mul_one] at h
  have hm : (coefficientEquiv e A).val = e.mapMatrix A.val := by ext i j; rfl
  simpa only [hm, mul_one] using h

public theorem coefficientMap_mem_GU2_iff
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (e : GaloisField p (2 * n) ≃+* GaloisField p (2 * n))
    (A : GL (Fin 2) (GaloisField p (2 * n))) :
    coefficientEquiv e A ∈ (unitaryForm 2 p n hn).unitarySubgroup ↔
      A ∈ (unitaryForm 2 p n hn).unitarySubgroup := by
  constructor
  · intro h
    have hback := coefficientMap_mem_GU2 p n hn e.symm (coefficientEquiv e A) h
    have heq : coefficientEquiv e.symm (coefficientEquiv e A) = A := by
      ext i j
      exact e.symm_apply_apply (A i j)
    rwa [heq] at hback
  · exact coefficientMap_mem_GU2 p n hn e A

@[expose] public noncomputable def GU2CoefficientEquiv
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (e : GaloisField p (2 * n) ≃+* GaloisField p (2 * n)) :
    GU2 p n hn ≃* GU2 p n hn where
  toFun A := ⟨coefficientEquiv e A.val,
    (coefficientMap_mem_GU2_iff p n hn e A.val).mpr A.property⟩
  invFun A := ⟨coefficientEquiv e.symm A.val,
    (coefficientMap_mem_GU2_iff p n hn e.symm A.val).mpr A.property⟩
  left_inv A := by apply Subtype.ext; exact (coefficientEquiv e).left_inv A.val
  right_inv A := by apply Subtype.ext; exact (coefficientEquiv e).right_inv A.val
  map_mul' A B := Subtype.ext ((coefficientEquiv e).map_mul A.val B.val)

@[expose] public noncomputable def GU2CoefficientAction
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)) →* MulAut (GU2 p n hn) where
  toFun := GU2CoefficientEquiv p n hn
  map_one' := by ext A; rfl
  map_mul' e f := by ext A; rfl

public abbrev GammaU2 (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :=
  GU2 p n hn ⋊[GU2CoefficientAction p n hn]
    (GaloisField p (2 * n) ≃+* GaloisField p (2 * n))

public theorem GU2CoefficientAction_mem_SU2Level_iff
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ)
    (e : GaloisField p (2 * n) ≃+* GaloisField p (2 * n)) (A : GU2 p n hn) :
    GU2CoefficientAction p n hn e A ∈ SU2Level p n hn m ↔ A ∈ SU2Level p n hn m := by
  exact coefficientAction_mem_determinantTwoPower_iff (GaloisField p (2 * n)) m e A.val

public theorem gammaU2_inr_conj_inl
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (e : GaloisField p (2 * n) ≃+* GaloisField p (2 * n)) (A : GU2 p n hn) :
    (SemidirectProduct.inr e : GammaU2 p n hn) * SemidirectProduct.inl A *
      (SemidirectProduct.inr e)⁻¹ =
      SemidirectProduct.inl (GU2CoefficientAction p n hn e A) := by
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut (φ := GU2CoefficientAction p n hn) e A).symm

public theorem SU2Level_semilinear_normal
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ) :
    ((SU2Level p n hn m).map
      (SemidirectProduct.inl : GU2 p n hn →* GammaU2 p n hn)).Normal := by
  let D := SU2Level p n hn m
  constructor
  rintro x ⟨A, hA, rfl⟩ g
  have hfield : GU2CoefficientAction p n hn g.right A ∈ D :=
    (GU2CoefficientAction_mem_SU2Level_iff p n hn m g.right A).mpr hA
  have hinner : g.left * GU2CoefficientAction p n hn g.right A * g.left⁻¹ ∈ D :=
    (inferInstance : D.Normal).conj_mem _ hfield g.left
  refine ⟨_, hinner, ?_⟩
  apply SemidirectProduct.ext
  · simp
  · simp

end ABG
