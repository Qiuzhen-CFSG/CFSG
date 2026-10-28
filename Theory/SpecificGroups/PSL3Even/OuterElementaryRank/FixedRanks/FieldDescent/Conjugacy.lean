module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldAction
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.ScalarNorm
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.LinearCocycle

/-!
# Removing the linear twist of a projective field involution

The involution equation on PSL₃ forces `g * σ(g)` to be scalar, and cyclic
permutation shows that scalar is fixed. Finite-field norm surjectivity
rescales g into a genuine matrix cocycle. Quadratic matrix Hilbert–90 then
produces a basis conjugating the literal projective actor to its field part.
Neither a scalar normalization nor a conjugator is assumed.

Adapted from the checked cubic argument in
`PSL3.StandardCubicFixedNine.Descent`. Source: GLS3, Theorem 2.5.12 and §2.7;
Aschbacher–Smith 16.1.4(4), printed p.1171.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
variable {F : Type*} [Field F]

private theorem map_two (σ : F ≃+* F) (hs : σ ^ 2 = 1) (m : GL (Fin 3) F) :
    GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m) = m := by
  apply Units.ext
  ext i j
  exact DFunLike.congr_fun hs (m.val i j)

private theorem scalar_injective : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ →* _) := by
  intro a b h
  apply Units.ext
  simpa using congrArg (fun g : GL (Fin 3) F => g.val 0 0) h

private theorem exists_scalar_square (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : σ ^ 2 = 1) (ha : (linearConj F m * fieldAction F σ) ^ 2 = 1) :
    ∃ c : Fˣ, m * GeneralLinearGroup.map σ.toRingHom m =
        GeneralLinearGroup.scalar (Fin 3) c ∧ Units.map σ.toRingHom c = c := by
  rw [linear_field_sq, hs, map_one, mul_one] at ha
  have hc : m * GeneralLinearGroup.map σ.toRingHom m ∈
      Subgroup.center (GL (Fin 3) F) := by
    rw [← Matrix.PSL3.ExtensionBorel.linearConj_ker]
    exact ha
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, hc.symm, scalar_injective ?_⟩
  rw [← GeneralLinearGroup.map_scalar, hc]
  simp only [map_mul, map_two σ hs]
  have he := congrArg (fun x => m⁻¹ * x * m) hc
  rw [← GeneralLinearGroup.scalar_commute c m⁻¹, mul_assoc, inv_mul_cancel, mul_one] at he
  simpa only [mul_assoc, inv_mul_cancel_left, hc] using he.symm

private theorem scalar_mul_mul (a b : Fˣ) (m n : GL (Fin 3) F) :
    (GeneralLinearGroup.scalar (Fin 3) a * m) *
      (GeneralLinearGroup.scalar (Fin 3) b * n) =
    GeneralLinearGroup.scalar (Fin 3) (a * b) * (m * n) := by
  rw [map_mul]
  exact (show Commute m (GeneralLinearGroup.scalar (Fin 3) b) from
    (GeneralLinearGroup.scalar_commute b m).symm).mul_mul_mul_comm _ _

private theorem rescale_square (m : GL (Fin 3) F) (σ : F ≃+* F) (c t : Fˣ)
    (hc : m * GeneralLinearGroup.map σ.toRingHom m =
        GeneralLinearGroup.scalar (Fin 3) c)
    (ht : t * Units.map σ.toRingHom.toMonoidHom t = c⁻¹) :
    let A := GeneralLinearGroup.scalar (Fin 3) t * m
    A * GeneralLinearGroup.map σ.toRingHom A = 1 := by
  dsimp only
  simp only [map_mul, GeneralLinearGroup.map_scalar]
  rw [scalar_mul_mul]
  change GeneralLinearGroup.scalar (Fin 3)
    (t * Units.map σ.toRingHom.toMonoidHom t) *
    (m * GeneralLinearGroup.map σ.toRingHom m) = 1
  rw [ht, hc, ← map_mul, inv_mul_cancel, map_one]

private theorem scalar_action (c : Fˣ) : linearConj F (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  apply (show GeneralLinearGroup.scalar (Fin 3) c ∈ (linearConj F).ker ↔ _ from Iff.rfl).mp
  rw [Matrix.PSL3.ExtensionBorel.linearConj_ker, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

private theorem conjugate_of_descent_matrix (m P : GL (Fin 3) F) (σ : F ≃+* F)
    (hP : m * GeneralLinearGroup.map σ.toRingHom P = P) :
    MulAut.congr (linearConj F P⁻¹) (linearConj F m * fieldAction F σ) = fieldAction F σ := by
  have hcongr : MulAut.congr (linearConj F P⁻¹) (linearConj F m * fieldAction F σ) =
      linearConj F P⁻¹ * (linearConj F m * fieldAction F σ) * linearConj F P := by
    ext x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply]
    rfl
  rw [hcongr, mul_assoc, mul_assoc, field_linearConj, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul]
  have he : P⁻¹ * m * GeneralLinearGroup.map σ.toRingHom P = 1 := by
    rw [mul_assoc, hP, inv_mul_cancel]
  rw [he, map_one, one_mul]

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent

namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
variable {F : Type*} [Field F] [Finite F]

/-- Every involutory linear–field actor with nontrivial field part is conjugate to its field factor by an
actual general linear conjugation. Scalar norm lifting handles the projective
kernel before applying matrix descent. -/
theorem exists_linear_conjugate_field (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : orderOf σ = 2) (ha : (linearConj F m * fieldAction F σ) ^ 2 = 1) :
    ∃ P : GL (Fin 3) F,
      MulAut.congr (linearConj F P) (linearConj F m * fieldAction F σ) = fieldAction F σ := by
  obtain ⟨c, hc, hfix⟩ := exists_scalar_square m σ (orderOf_eq_prime_iff.mp hs).1 ha
  obtain ⟨t, ht⟩ := exists_quadratic_norm σ hs c⁻¹ (by rw [map_inv]; exact congrArg (fun u : Fˣ => u⁻¹) hfix)
  let A := GeneralLinearGroup.scalar (Fin 3) t * m
  obtain ⟨P, hP⟩ := linear_cocycle_descent σ hs A (rescale_square m σ c t hc ht)
  refine ⟨P⁻¹, ?_⟩
  have he : linearConj F A = linearConj F m := by
    simp only [A, map_mul, scalar_action, one_mul]
  rw [← he]
  exact conjugate_of_descent_matrix A P σ hP

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
