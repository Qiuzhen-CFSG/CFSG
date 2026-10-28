module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.Setup
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear

/-!
# Diagonal coordinates for the pointwise standard-four fixer

The shared formula retains arbitrary norm-one diagonal units, including
outer diagonal automorphisms. Its action is specified in the actual PGL
image. The norm equations give genuine unitary matrices, while commutation
of diagonal matrices and invariance of signs under field automorphisms
show that every such formula fixes the standard four-group pointwise.

The converse placement and normalization of entire two-subgroups are separate
calculations. These are coordinate interfaces for Aschbacher--Smith E.1.14(7),
printed p.214, A.3.21(a)--(b), printed p.55, and Aschbacher (1982), Lemma 4.11.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]
open UnitaryThree.OddTorusNormalizer

/-- A literal diagonal unitary representative and either identity or the stored
Hermitian field action, acting on the actual projective special image. -/
@[expose] def HasDiagonalSemilinearForm (J : HermitianForm 3 F)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ (d : Fin 3 → Fˣ) (σ : F ≃+* F),
    (∀ i, J.conj (d i : F) * (d i : F) = 1) ∧ (σ = 1 ∨ σ = J.conj) ∧
    ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk (diagonalHom d) *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk (diagonalHom d))⁻¹

namespace StandardFixer

/-- The exact scalar norm equations for a diagonal unitary matrix. -/
theorem diagonal_mem_unitary (J : HermitianForm 3 F) (hJ : J.form = 1)
    (d : Fin 3 → Fˣ) :
    diagonalHom d ∈ J.unitarySubgroup ↔ ∀ i, J.conj (d i : F) * (d i : F) = 1 := by
  rw [J.mem_unitarySubgroup_iff, hJ, mul_one]
  have ha : J.conjTranspose (diagonalHom d).val =
      Matrix.diagonal (fun i => J.conj (d i : F)) := by
    ext i j
    by_cases h : i = j <;> simp [HermitianForm.conjTranspose, diagonalHom, h, Ne.symm]
  rw [ha]
  change Matrix.diagonal (fun i => J.conj (d i : F)) * Matrix.diagonal (fun i => (d i : F)) = 1 ↔ _
  rw [Matrix.diagonal_mul_diagonal]
  constructor
  · intro h i
    simpa using congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i i) h
  · intro h
    simp only [h, Matrix.diagonal_one]

/-- A diagonal matrix of norm-one units in the identity Gram unitary group. -/
@[expose] def diagonalUnitary (J : HermitianForm 3 F) (hJ : J.form = 1)
    (d : Fin 3 → Fˣ) (hd : ∀ i, J.conj (d i : F) * (d i : F) = 1) :
    J.unitarySubgroup := ⟨diagonalHom d, (diagonal_mem_unitary J hJ d).2 hd⟩

/-- Every coefficient-field automorphism fixes the literal sign matrices. -/
theorem map_signGL (σ : F ≃+* F) (ε : Fin 3 → Bool) :
    GeneralLinearGroup.map σ.toRingHom (signGL ε) = signGL ε := by
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : ε i <;> simp [signGL, diagonalHom, h]
  · simp [signGL, diagonalHom, hij]

/-- Diagonal matrices commute with each literal sign matrix before quotienting. -/
theorem diagonal_commute_signGL (d : Fin 3 → Fˣ) (ε : Fin 3 → Bool) :
    Commute (diagonalHom d) (signGL ε : GL (Fin 3) F) :=
  (Commute.all d (fun i => if ε i then -1 else 1)).map diagonalHom

/-- A diagonal semilinear formula fixes the entire generated standard four-group. -/
theorem diagonal_formula_fixes_standardFour (J : HermitianForm 3 F)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (d : Fin 3 → Fˣ) (σ : F ≃+* F)
    (ha : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk (diagonalHom d) *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk (diagonalHom d))⁻¹) :
    ∀ x ∈ standardFour J, a x = x := by
  apply MonoidHom.eqOn_closure (f := a.toMonoidHom) (g := MonoidHom.id _)
  rintro x ⟨ε, hε⟩
  apply Subtype.ext
  change (a x).val = x.val
  rw [ha, hε, ProjGenLinGroup.map_mk, map_signGL]
  have hh := (diagonal_commute_signGL d ε).map ProjGenLinGroup.mk
  rw [hh.eq, mul_inv_cancel_right]

/-- In particular, a diagonal unitary conjugator preserves the marked four-group pointwise. -/
theorem diagonalUnitary_conj_fixes_standardFour (J : HermitianForm 3 F)
    (hJ : J.form = 1) (d : Fin 3 → Fˣ)
    (hd : ∀ i, J.conj (d i : F) * (d i : F) = 1) :
    ∀ x ∈ standardFour J, J.unitaryConj (diagonalUnitary J hJ d hd) x = x := by
  apply diagonal_formula_fixes_standardFour J _ d 1
  intro x
  rw [J.unitaryConj_apply_val]
  change _ = _ * ProjGenLinGroup.map (RingHom.id F) x.val * _
  rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
  rfl

end StandardFixer

/-- Diagonal coordinates imply literal pointwise fixation of the standard four-group. -/
theorem HasDiagonalSemilinearForm.fixes_standardFour {J : HermitianForm 3 F}
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (ha : HasDiagonalSemilinearForm J a) :
    ∀ x ∈ standardFour J, a x = x := by
  obtain ⟨d, σ, _, _, h⟩ := ha
  exact StandardFixer.diagonal_formula_fixes_standardFour J a d σ h

/-- The diagonal coordinate contract gives a genuine unitary semilinear formula. -/
theorem HasDiagonalSemilinearForm.unitary {J : HermitianForm 3 F} (hJ : J.form = 1)
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (ha : HasDiagonalSemilinearForm J a) :
    ∃ σ : F ≃+* F, (σ = 1 ∨ σ = J.conj) ∧ J.HasUnitarySemilinearForm a σ := by
  obtain ⟨d, σ, hd, hσ, h⟩ := ha
  exact ⟨σ, hσ, StandardFixer.diagonalUnitary J hJ d hd, h⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
