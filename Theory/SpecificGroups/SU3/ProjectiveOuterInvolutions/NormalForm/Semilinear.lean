module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# Concrete unitary-semilinear formulas on projective SU₃

A unitary-semilinear formula describes an automorphism on the actual subgroup
of PGL: apply a field automorphism to matrix entries, then conjugate by a
unitary matrix. The formula is closed under composition. Its identity-field
case is unitary conjugation, and its Hermitian-field case is a unitary twist of
the specified entrywise conjugation.

The two separate structural questions are whether every automorphism admits
such a formula, and whether a formula for the identity has trivial field part.
Neither is assumed by the definition or proved by the composition lemma.
They are the matrix forms of the coverage and splitting assertions in GLS,
Volume 3, Theorem 2.5.12(a,d,f), using Section 2.7's identification
`Inndiag(PSU₃(q)) = PGU₃(q)`.
-/

namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- An equality in the actual ambient PGL specifies both the unitary conjugating
matrix and the entrywise field action. -/
@[expose] public def HasUnitarySemilinearForm
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : E ≃+* E) : Prop :=
  ∃ u : J.unitarySubgroup, ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
    (a b).val = Matrix.ProjGenLinGroup.mk u.val *
      Matrix.ProjGenLinGroup.map σ.toRingHom b.val *
      (Matrix.ProjGenLinGroup.mk u.val)⁻¹

private theorem field_map_unitary [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (σ : E ≃+* E) (u : J.unitarySubgroup) :
    Matrix.GeneralLinearGroup.map σ.toRingHom u.val ∈ J.unitarySubgroup := by
  have hform : J.form.map σ = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hadj : J.conjTranspose (u.val.val.map σ) = (J.conjTranspose u.val.val).map σ := by
    let := finiteFieldAut_isCyclic (E := E)
    let := IsCyclic.commGroup (α := E ≃+* E)
    ext i j
    exact congrArg (fun f : E ≃+* E => f (u.val.val j i)) (Commute.all J.conj σ).eq
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map σ) * J.form * u.val.val.map σ = J.form
  rw [hadj, ← hform, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map σ)
    ((J.mem_unitarySubgroup_iff _).mp u.property)

private theorem projective_field_mul (σ τ : E ≃+* E)
    (b : Matrix.ProjGenLinGroup (Fin 3) E) :
    Matrix.ProjGenLinGroup.map (σ * τ).toRingHom b =
      Matrix.ProjGenLinGroup.map σ.toRingHom (Matrix.ProjGenLinGroup.map τ.toRingHom b) := by
  change Matrix.ProjGenLinGroup.map (σ.toRingHom.comp τ.toRingHom) b = _
  rw [Matrix.ProjGenLinGroup.map_comp]
  rfl

/-- Multiplication of concrete semilinear formulas multiplies their field parts. -/
public theorem HasUnitarySemilinearForm.mul [Finite E]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {a b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ τ : E ≃+* E}
    (ha : J.HasUnitarySemilinearForm a σ) (hb : J.HasUnitarySemilinearForm b τ) :
    J.HasUnitarySemilinearForm (a * b) (σ * τ) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  let w : J.unitarySubgroup :=
    ⟨Matrix.GeneralLinearGroup.map σ.toRingHom v.val, field_map_unitary J hJ σ v⟩
  refine ⟨u * w, ?_⟩
  intro x
  change (a (b x)).val =
    Matrix.ProjGenLinGroup.mk (u.val * Matrix.GeneralLinearGroup.map σ.toRingHom v.val) *
      Matrix.ProjGenLinGroup.map (σ * τ).toRingHom x.val *
      (Matrix.ProjGenLinGroup.mk (u.val * Matrix.GeneralLinearGroup.map σ.toRingHom v.val))⁻¹
  rw [hu, hv, projective_field_mul]
  simp [map_mul, map_inv, mul_assoc]

/-- A formula with trivial field part is precisely a unitary conjugation. -/
public theorem HasUnitarySemilinearForm.one_iff
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} :
    J.HasUnitarySemilinearForm a 1 ↔ ∃ u : J.unitarySubgroup, a = J.unitaryConj u := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, MulEquiv.ext fun b => Subtype.ext ?_⟩
    rw [J.unitaryConj_apply_val, hu]
    change _ * Matrix.ProjGenLinGroup.map (RingHom.id E) b.val * _ = _
    rw [Matrix.ProjGenLinGroup.map_id, MonoidHom.id_apply]
  · rintro ⟨u, rfl⟩
    refine ⟨u, fun b => ?_⟩
    change _ = _ * Matrix.ProjGenLinGroup.map (RingHom.id E) b.val * _
    rw [Matrix.ProjGenLinGroup.map_id, MonoidHom.id_apply]
    exact J.unitaryConj_apply_val u b

/-- The representative specification of Hermitian conjugation also determines
its action on the ambient projective matrix image. -/
public theorem IsEntrywiseConjugation.apply_val
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (γ b).val = Matrix.ProjGenLinGroup.map J.conj.toRingHom b.val := by
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  obtain ⟨y, hy, hxy⟩ := hγ x
  rw [hxy, J.specialToProjective_apply_val, J.specialToProjective_apply_val,
    Matrix.ProjGenLinGroup.map_mk]
  exact congrArg Matrix.ProjGenLinGroup.mk (Units.ext hy)

/-- A formula whose field part is the Hermitian involution is exactly the
unitary twist required by the outer-involution normal form. -/
public theorem HasUnitarySemilinearForm.conj_iff
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} :
    J.HasUnitarySemilinearForm a J.conj ↔
      ∃ u : J.unitarySubgroup, a = J.unitaryConj u * γ := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, MulEquiv.ext fun b => Subtype.ext ?_⟩
    change (a b).val = (J.unitaryConj u (γ b)).val
    rw [hu, J.unitaryConj_apply_val, hγ.apply_val]
  · rintro ⟨u, rfl⟩
    refine ⟨u, fun b => ?_⟩
    change (J.unitaryConj u (γ b)).val = _
    rw [J.unitaryConj_apply_val, hγ.apply_val]

end BenderSuzuki.MatrixGroups.HermitianForm
