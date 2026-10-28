module

public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Conditional
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Descent.ScalarNorm
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Descent.LinearCocycle

/-!
# Projective cubic semilinear descent for PSL₃

Let σ have order three and let the actor `linearConj m * fieldAction σ`
have cube one on the actual central quotient of SL₃. Compatibility of the
matrix actions and their scalar kernel imply that `m * σ(m) * σ²(m)` is
scalar. Cyclic permutation shows that this scalar is fixed by σ. Lift its
inverse through the finite-field norm and rescale m to obtain a genuine
matrix cocycle. Cubic matrix Hilbert–90 then supplies an invertible descent
basis, whose inverse conjugates the projective actor to `fieldAction σ`.

Thus the conjugator is itself induced by GL₃. No splitting of mixed
field–diagonal cosets and no cube-one matrix representative are assumed.
The final theorem applies the parent's fixed-nine transport to this exact
linear–field actor, with every descent premise discharged.

Source: GLS3, Proposition 4.9.1(d), `refs/KGroup/GLS3/chapter4.tex`,
lines 2950–2978; the literal matrix conventions are those of Theorem 2.5.12
and §2.7. This is the conjugacy assertion used by Aschbacher–Smith,
`refs/quasithin.pdf`, A.3.16–18, printed pp.51–53, and 15.3.37, p.1135.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.StandardCubicFixedNine.Descent
variable {F : Type*} [Field F]

private theorem map_three (σ : F ≃+* F) (hs : σ ^ 3 = 1) (m : GL (Fin 3) F) :
    GeneralLinearGroup.map σ.toRingHom
      (GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m)) = m := by
  apply Units.ext
  ext i j
  exact DFunLike.congr_fun hs (m.val i j)

private theorem cube_formula (m : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F m * fieldAction F σ) ^ 3 =
      linearConj F (m * GeneralLinearGroup.map σ.toRingHom m *
        GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m)) *
      fieldAction F σ ^ 3 := by
  let L := linearConj F
  let S := fieldAction F σ
  change (L m * S) ^ 3 = _
  calc
    (L m * S) ^ 3 = L m * (S * L m) * (S * L m) * S := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = L m * (L (GeneralLinearGroup.map σ.toRingHom m) * S) *
        (L (GeneralLinearGroup.map σ.toRingHom m) * S) * S := by
      rw [field_linearConj]
    _ = (L m * L (GeneralLinearGroup.map σ.toRingHom m)) *
        (S * L (GeneralLinearGroup.map σ.toRingHom m)) * S * S := by group
    _ = _ := by
      rw [field_linearConj]
      simp only [L, S, map_mul, pow_succ, pow_zero, one_mul, mul_assoc]

private theorem scalar_injective : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ →* _) := by
  intro a b h
  apply Units.ext
  simpa using congrArg (fun g : GL (Fin 3) F => g.val 0 0) h

private theorem exists_scalar_cube (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : σ ^ 3 = 1) (ha : (linearConj F m * fieldAction F σ) ^ 3 = 1) :
    ∃ c : Fˣ, m * GeneralLinearGroup.map σ.toRingHom m *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m) =
        GeneralLinearGroup.scalar (Fin 3) c ∧ Units.map σ.toRingHom c = c := by
  rw [cube_formula, ← map_pow, hs, map_one, mul_one] at ha
  have hc : m * GeneralLinearGroup.map σ.toRingHom m *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m) ∈
      Subgroup.center (GL (Fin 3) F) := by
    rw [← ExtensionBorel.linearConj_ker]
    exact ha
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, hc.symm, scalar_injective ?_⟩
  rw [← GeneralLinearGroup.map_scalar, hc]
  simp only [map_mul, map_three σ hs]
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

private theorem rescale_cube (m : GL (Fin 3) F) (σ : F ≃+* F) (c t : Fˣ)
    (hc : m * GeneralLinearGroup.map σ.toRingHom m *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m) =
        GeneralLinearGroup.scalar (Fin 3) c)
    (ht : t * Units.map σ.toRingHom.toMonoidHom t *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t) = c⁻¹) :
    let A := GeneralLinearGroup.scalar (Fin 3) t * m
    A * GeneralLinearGroup.map σ.toRingHom A *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom A) = 1 := by
  dsimp only
  simp only [map_mul, GeneralLinearGroup.map_scalar]
  rw [scalar_mul_mul, scalar_mul_mul]
  change GeneralLinearGroup.scalar (Fin 3)
    (t * Units.map σ.toRingHom.toMonoidHom t *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom t)) *
    (m * GeneralLinearGroup.map σ.toRingHom m *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom m)) = 1
  rw [ht, hc, ← map_mul, inv_mul_cancel, map_one]

private theorem scalar_action (c : Fˣ) : linearConj F (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  apply (show GeneralLinearGroup.scalar (Fin 3) c ∈ (linearConj F).ker ↔ _ from Iff.rfl).mp
  rw [ExtensionBorel.linearConj_ker, GeneralLinearGroup.center_eq_range_scalar]
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

end Matrix.PSL3.StandardCubicFixedNine.Descent

namespace Matrix.PSL3.StandardCubicFixedNine.Descent
variable {F : Type*} [Field F] [Finite F]

/-- Every cubic linear–field actor is conjugate to its field factor by an
actual general linear conjugation. Scalar norm lifting handles the projective
kernel before applying matrix descent. -/
theorem exists_linear_conjugate_field (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : orderOf σ = 3) (ha : (linearConj F m * fieldAction F σ) ^ 3 = 1) :
    ∃ P : GL (Fin 3) F,
      MulAut.congr (linearConj F P) (linearConj F m * fieldAction F σ) = fieldAction F σ := by
  obtain ⟨c, hc, hfix⟩ := exists_scalar_cube m σ (orderOf_eq_prime_iff.mp hs).1 ha
  obtain ⟨t, ht⟩ := exists_cubic_norm σ hs c⁻¹ (by rw [map_inv]; exact congrArg (fun u : Fˣ => u⁻¹) hfix)
  let A := GeneralLinearGroup.scalar (Fin 3) t * m
  obtain ⟨P, hP⟩ := linear_cocycle_descent σ hs A (rescale_cube m σ c t hc ht)
  refine ⟨P⁻¹, ?_⟩
  have he : linearConj F A = linearConj F m := by
    simp only [A, map_mul, scalar_action, one_mul]
  rw [← he]
  exact conjugate_of_descent_matrix A P σ hP

/-- Projective cubic semilinear descent on the actual matrix quotient PSL₃.
This stronger form needs only finiteness of the field, without characteristic
or degree restrictions. -/
theorem exists_conjugate_field (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : orderOf σ = 3) (ha : (linearConj F m * fieldAction F σ) ^ 3 = 1) :
    ∃ d : MulAut PSL(3,F),
      MulAut.congr d (linearConj F m * fieldAction F σ) = fieldAction F σ := by
  obtain ⟨P, hP⟩ := exists_linear_conjugate_field m σ hs ha
  exact ⟨linearConj F P, hP⟩

/-- Concrete consumer: the cubic linear–field actor fixes an inner nine-group
under the inherited simplicity and nonsolvability hypotheses. This discharges
the conjugacy premise of `exists_fixed_inner_nine_of_conjugate_field`. -/
theorem exists_fixed_inner_nine [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n)
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hs : orderOf σ = 3) (ha : (linearConj F m * fieldAction F σ) ^ 3 = 1) :
    ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.centralizer ({linearConj F m * fieldAction F σ} : Set (MulAut PSL(3,F))) := by
  obtain ⟨d, hd⟩ := exists_conjugate_field m σ hs ha
  exact exists_fixed_inner_nine_of_conjugate_field hns hcard hn
    (linearConj F m * fieldAction F σ) d σ (orderOf_eq_prime_iff.mp hs).1 hd

end Matrix.PSL3.StandardCubicFixedNine.Descent
