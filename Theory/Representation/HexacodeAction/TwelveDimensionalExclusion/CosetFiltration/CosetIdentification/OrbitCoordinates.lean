module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.Words

/-!
# Central-orbit coordinates in the literal permutation module

An eigenvector for the marked cubic is determined by one coefficient per
central orbit. Extending these coefficients by the powers of omega² gives
the inverse map. The inverse-action row equations then prove equivariance
for both marked generators. This constructs a linear equivalence with the
actual subspace, without any irreducibility or filtration hypothesis.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification

/-- The literal omega-eigenspace, viewed as a vector subspace. -/
noncomputable abbrev Eigenspace (P : Subgroup Cover) :=
  (centralEigenspace (cosetRepresentation P)).toSubmodule

private theorem cubic : hexEvenZ ^ 3 = 1 := by
  rw [← hexEvenZ_order, pow_orderOf_eq_one]

private theorem cubic_inv : hexEvenZ⁻¹ = hexEvenZ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using cubic

private theorem orbitPoint_pred {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (i : Fin 45) (k : Fin 3) :
    hexEvenZ⁻¹ • orbitPoint q (i, k) = orbitPoint q (i, k - 1) := by
  fin_cases k
  · simp only [orbitPoint, pow_zero, one_smul, cubic_inv]
    rfl
  · change hexEvenZ⁻¹ • (hexEvenZ ^ 1 • q i) = hexEvenZ ^ 0 • q i
    simp
  · change hexEvenZ⁻¹ • (hexEvenZ ^ 2 • q i) = hexEvenZ ^ 1 • q i
    rw [pow_two, mul_smul, inv_smul_smul, pow_one]

private theorem weight_pred (k : Fin 3) : weight (k - 1) = omega * weight k := by
  revert k
  decide +kernel

/-- Coefficients of an omega-eigenvector along one central orbit. -/
theorem eigenvector_coeff_pow {P : Subgroup Cover} (v : Eigenspace P)
    (x : Cover ⧸ P) (n : ℕ) :
    v.val.coeff (hexEvenZ ^ n • x) = (omega ^ 2) ^ n * v.val.coeff x := by
  have step (y : Cover ⧸ P) : v.val.coeff (hexEvenZ • y) =
      omega ^ 2 * v.val.coeff y := by
    have hv : cosetRepresentation P hexEvenZ v.val = omega • v.val := v.property
    have he := congrArg (fun w => w.coeff (hexEvenZ • y)) hv
    rw [Representation.coeff_ofMulAction, inv_smul_smul,
      MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at he
    rw [he, ← mul_assoc, show omega ^ 2 * omega = (1 : F) by decide, one_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' hexEvenZ, mul_smul, step, ih, pow_succ' (omega ^ 2), mul_assoc]

/-- Read the coefficient of each selected left coset. -/
def sample {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P) : Eigenspace P →ₗ[F] Space where
  toFun v i := v.val.coeff (q i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sample_injective {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Surjective (orbitPoint q)) : Function.Injective (sample q) := by
  intro v w h
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  obtain ⟨⟨i, k⟩, rfl⟩ := hq x
  change v.val.coeff (hexEvenZ ^ k.val • q i) = w.val.coeff (hexEvenZ ^ k.val • q i)
  rw [eigenvector_coeff_pow, eigenvector_coeff_pow]
  exact congrArg ((omega ^ 2) ^ k.val * ·) (congrFun h i)

/-- Extend the selected coefficients with the forced central-character weights. -/
noncomputable def extendVector {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (v : Space) : MonoidAlgebra F (Cover ⧸ P) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun x =>
    let a := (Equiv.ofBijective (orbitPoint q) hq).symm x
    weight a.2 * v a.1))

theorem extendVector_coeff {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (v : Space) (i : Fin 45) (k : Fin 3) :
    (extendVector q hq v).coeff (orbitPoint q (i, k)) = weight k * v i := by
  change (fun a : Fin 45 × Fin 3 => weight a.2 * v a.1)
    ((Equiv.ofBijective (orbitPoint q) hq).symm
      ((Equiv.ofBijective (orbitPoint q) hq) (i, k))) = _
  rw [_root_.Equiv.symm_apply_apply]

theorem extendVector_mem {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (v : Space) :
    extendVector q hq v ∈ Eigenspace P := by
  change cosetRepresentation P hexEvenZ (extendVector q hq v) = omega • extendVector q hq v
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  obtain ⟨⟨i, k⟩, rfl⟩ := hq.2 x
  rw [Representation.coeff_ofMulAction, orbitPoint_pred, extendVector_coeff,
    MonoidAlgebra.coeff_smul_apply, extendVector_coeff, smul_eq_mul, weight_pred, mul_assoc]

theorem sample_surjective {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) : Function.Surjective (sample q) := by
  intro v
  refine ⟨⟨extendVector q hq v, extendVector_mem q hq v⟩, ?_⟩
  funext i
  change (extendVector q hq v).coeff (q i) = v i
  have h := extendVector_coeff q hq v i 0
  simpa only [orbitPoint, Fin.val_zero, pow_zero, one_smul, weight, one_mul] using h

/-- An actual linear equivalence onto the omega-eigenspace of the coset module. -/
noncomputable def orbitCoordinates {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) : Space ≃ₗ[F] Eigenspace P :=
  (LinearEquiv.ofBijective (sample q) ⟨sample_injective q hq.2, sample_surjective q hq⟩).symm

theorem sample_orbitCoordinates {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (v : Space) :
    sample q (orbitCoordinates q hq v) = v :=
  (LinearEquiv.ofBijective (sample q)
    ⟨sample_injective q hq.2, sample_surjective q hq⟩).apply_symm_apply v

theorem orbitCoordinates_coeff {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (v : Space) (i : Fin 45) (k : Fin 3) :
    (orbitCoordinates q hq v).val.coeff (orbitPoint q (i, k)) = weight k * v i := by
  change (orbitCoordinates q hq v).val.coeff (hexEvenZ ^ k.val • q i) = _
  rw [eigenvector_coeff_pow]
  exact congrArg (weight k * ·) (congrFun (sample_orbitCoordinates q hq v) i)

theorem orbitCoordinates_generator {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q))
    (htrans : ∀ j i, (coverGenerator j)⁻¹ • q i =
      orbitPoint q (rowSource j i, phase j i)) (j : Fin 2) (v : Space) :
    orbitCoordinates q hq (generator j v) =
      cosetCentralRepresentation P (coverGenerator j) (orbitCoordinates q hq v) := by
  apply sample_injective q hq.2
  rw [sample_orbitCoordinates]
  funext i
  change coefficient j i * v (rowSource j i) =
    (cosetRepresentation P (coverGenerator j) (orbitCoordinates q hq v).val).coeff (q i)
  rw [Representation.coeff_ofMulAction, htrans, orbitCoordinates_coeff, weight_phase]

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification
