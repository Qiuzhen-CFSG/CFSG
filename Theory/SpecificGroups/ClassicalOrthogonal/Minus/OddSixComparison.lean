module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Quotient
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.SignedCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image

/-!
# The odd minus-six comparison: projective assembly

The signed exterior realization on the original minus-six quadratic space
and its proved projective image identify PΩ⁻₆(F) with PSU₄(q). The matrix
field has order q² and conjugation is exactly the q-power automorphism.
Odd unitary perfectness supplies containment in the full-isometry commutator;
the lifted Siegel subgroup and inherited projective simplicity give
surjectivity. The exact scalar-kernel theorem then identifies the two literal
projective carriers, including at q = 3.

`projectiveEquiv` and `exists_projectiveEquivPSU` discharge all geometry and
image premises. Simplicity is assumed only for the original projective carrier,
as supplied by the source's simple ambient group. The earlier conditional
comparison and its diagonal nontriviality witness remain available.
Source: GLS3 §2.7 and the dimension reduction in Aschbacher–Smith A.2.17,
printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups Theory.SpecificGroups.ClassicalUnitary

section PrimePower
variable (p n : ℕ) [Fact p.Prime] [NeZero n]

private def signMatrix : Matrix (Fin 4) (Fin 4) (Extension p n) :=
  Matrix.diagonal ![-1, 1, 1, -1]

omit [NeZero n] in
private theorem signMatrix_sq : signMatrix p n * signMatrix p n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signMatrix, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A determinant-one antidiagonal unitary matrix, nonscalar in odd characteristic. -/
def signElement : (unitaryForm p n).specialSubgroup := by
  have hct : (unitaryForm p n).conjTranspose (signMatrix p n) = signMatrix p n := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [signMatrix, HermitianForm.conjTranspose, Matrix.diagonal_apply_eq]
      fin_cases i <;> simp
    · simp only [signMatrix, HermitianForm.conjTranspose, Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]
  refine ⟨⟨signMatrix p n, signMatrix p n, signMatrix_sq p n, signMatrix_sq p n⟩, ?_, ?_⟩
  · change (unitaryForm p n).conjTranspose (signMatrix p n) *
      (unitaryForm p n).form * signMatrix p n = (unitaryForm p n).form
    rw [hct]
    change signMatrix p n * UnitaryFourFlag.gram (Extension p n) * signMatrix p n = _
    ext i j
    simp only [signMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> norm_num [UnitaryFourFlag.gram, unitaryForm, UnitaryFourFlag.form]
  · apply Units.ext
    change (signMatrix p n).det = 1
    simp [signMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- This witness survives the literal SU₄ → PSU₄ projection. -/
theorem signElement_project_ne_one (hp : p ≠ 2) :
    UnitaryFourFlag.project (Extension p n) (unitaryForm p n) (signElement p n) ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := (unitary_project_eq_one_iff_scalar _).mp h
  have h0 := congrArg (fun A : Matrix (Fin 4) (Fin 4) (Extension p n) => A 0 0) ha
  have h1 := congrArg (fun A : Matrix (Fin 4) (Fin 4) (Extension p n) => A 1 1) ha
  change signMatrix p n 0 0 = _ at h0
  change signMatrix p n 1 1 = _ at h1
  simp only [signMatrix, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have htwo : (2 : Extension p n) = 0 := by linear_combination h1 - h0
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (Extension p n) p 2).mp htwo
  exact hp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one)

variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (hcomm : ∀ g, R.action g ∈ commutator (FullOrthogonal F))

/-- Nontriviality of the projective exterior image is explicit, not assumed. -/
theorem ExteriorRealization.projectiveAction_range_ne_bot (hp : p ≠ 2) :
    (R.projectiveAction hcomm).range ≠ ⊥ := by
  intro hbot
  have hg : R.projectiveAction hcomm (signElement p n) = 1 := by
    have hm : R.projectiveAction hcomm (signElement p n) ∈
        (R.projectiveAction hcomm).range := ⟨signElement p n, rfl⟩
    simpa only [hbot, Subgroup.mem_bot] using hm
  exact signElement_project_ne_one p n hp ((R.projectiveAction_eq_one_iff hcomm _).mp hg)

/-- Only geometric realization and commutator/normality inputs remain;
all scalar-kernel and projective-surjectivity steps are proved. -/
def ExteriorRealization.projectiveEquiv_of_normal (hp : p ≠ 2)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (hN : (R.projectiveAction hcomm).range.Normal) :
    ClassicalGroup.POmegaMinus 3 F ≃*
      ProjectiveSpecialUnitaryMatrixGroup (unitaryForm p n) :=
  R.projectiveEquiv_of_surjective hcomm
    (R.projectiveAction_surjective_of_normal hcomm hN
      (R.projectiveAction_range_ne_bot p n hcomm hp))

/-- The conditional comparison acts through the original two projective maps. -/
@[simp] theorem ExteriorRealization.projectiveEquiv_of_normal_apply (hp : p ≠ 2)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (hN : (R.projectiveAction hcomm).range.Normal)
    (g : (unitaryForm p n).specialSubgroup) :
    R.projectiveEquiv_of_normal p n hcomm hp hN (R.projectiveAction hcomm g) =
      UnitaryFourFlag.project (Extension p n) (unitaryForm p n) g :=
  R.projectiveEquiv_of_surjective_apply _ _ _

/-- The actual minus-six carrier is PSU₄ over the quadratic extension, with all
descent, coordinate transport, commutator and projective image inputs discharged. -/
def projectiveEquiv (hp : p ≠ 2) (hcard : Nat.card F = p ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)] :
    ClassicalGroup.POmegaMinus 3 F ≃*
      ProjectiveSpecialUnitaryMatrixGroup (unitaryForm p n) :=
  (Geometry.realization p n F hcard).projectiveEquiv_of_signedCoordinates
    (Geometry.signedCoordinates p n F hcard) hp

/-- On the constructed exterior action, the comparison is the original SU₄
projection into PSU₄. Both projective maps retain their literal scalar kernels. -/
@[simp] theorem projectiveEquiv_apply (hp : p ≠ 2) (hcard : Nat.card F = p ^ n)
    [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]
    (g : (unitaryForm p n).specialSubgroup) :
    projectiveEquiv p n hp hcard
        ((Geometry.realization p n F hcard).projectiveAction
          ((Geometry.realization p n F hcard).action_mem_commutator hp) g) =
      UnitaryFourFlag.project (Extension p n) (unitaryForm p n) g :=
  (Geometry.realization p n F hcard).projectiveEquiv_of_signedCoordinates_apply
    (Geometry.signedCoordinates p n F hcard) hp g

end PrimePower

variable (F : Type) [Field F] [Finite F]
variable [IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F)]

/-- Every odd finite coefficient field supplies the actual unitary comparison,
with matrix-field order q² and conjugation x ↦ x^q. Its prime-power presentation
is obtained from the field itself; no geometric or image premise remains. -/
theorem exists_projectiveEquivPSU (ho : Odd (Nat.card F)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 4 E),
      Nat.card E = (Nat.card F) ^ 2 ∧ (∀ x, J.conj x = x ^ Nat.card F) ∧
        Nonempty (ClassicalGroup.POmegaMinus 3 F ≃*
          ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff (Fintype.card F)).mp
    (FiniteField.isPrimePow_card F)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcard : Nat.card F = p ^ n := by
    simpa only [Nat.card_eq_fintype_card] using hpn.symm
  have hp2 : p ≠ 2 := by
    intro he
    apply ho.not_two_dvd_nat
    rw [hcard, he]
    exact dvd_pow_self 2 (NeZero.ne n)
  refine ⟨Extension p n, inferInstance, inferInstance, unitaryForm p n, ?_, ?_,
    ⟨projectiveEquiv p n hp2 hcard⟩⟩
  · rw [hcard]
    exact card_extension p n
  · intro x
    rw [hcard]
    exact unitaryForm_conj p n x

end ClassicalOrthogonal.Minus.OddSixComparison
