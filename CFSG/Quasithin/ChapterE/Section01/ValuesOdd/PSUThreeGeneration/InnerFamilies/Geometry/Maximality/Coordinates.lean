module

public import Theory.SpecificGroups.SU3.FullCentralizer

/-!
# Orthogonal-line reduction for odd PSU₃ centralizer maximality

The coordinate cycle is a concrete determinant-one isometry moving the third
coordinate line to an orthogonal line. In characteristic different from two,
every matrix whose last diagonal entry vanishes lies outside the centralizer
of `diag(-1,-1,1)`, so that centralizer is proper.

Two independent geometric inputs suffice for maximality: every strictly larger
subgroup contains such an orthogonal displacement, and the centralizers of the
two resulting orthogonal lines generate SU₃. The final theorem proves this
implication only; the two matrix inputs remain explicit and must be constructed.
The entry condition uses the identity Hermitian form and the actual SU matrices.

Source: the unitary geometry for Aschbacher--Smith, E.1.14(7), printed p.214,
and A.3.21(a), printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
variable {F : Type*} [Field F]

/-- The coordinate cycle sends the distinguished third line to the first line. -/
@[expose] def coordinateCycle (J : HermitianForm 3 F) (hJ : J.form = 1) :
    J.specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    (by simp [Matrix.det_fin_three]), by
      rw [J.mem_specialSubgroup_iff, hJ]
      constructor
      · change J.conjTranspose !![0, 0, 1; 1, 0, 0; 0, 1, 0] * 1 *
          !![0, 0, 1; 1, 0, 0; 0, 1, 0] = 1
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]
      · apply Units.ext
        simp [GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]⟩

theorem coordinateCycle_last_diagonal (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (coordinateCycle J hJ).val.val 2 2 = 0 := rfl

theorem zero_last_diagonal_not_centralizer (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (g : J.specialSubgroup) (hg : g.val.val 2 2 = 0) :
    g ∉ centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) := by
  intro hm
  have he := congrArg (fun a : J.specialSubgroup => a.val.val)
    (mem_centralizer_singleton_iff.mp hm)
  change g.val.val * (SU3.standardInvolution J hJ).val.val =
    (SU3.standardInvolution J hJ).val.val * g.val.val at he
  rw [SU3.standardInvolution_val] at he
  have h02 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 2) he
  have h12 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 1 2) he
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02 h12
  have hz (x : F) (hx : 2 * x = 0) : x = 0 := (mul_eq_zero.mp hx).resolve_left h2
  have h02' : g.val.val 0 2 = 0 := hz _ (by linear_combination h02)
  have h12' : g.val.val 1 2 = 0 := hz _ (by linear_combination h12)
  exact g.val.det_ne_zero (by simp [Matrix.det_fin_three, h02', h12', hg])

theorem standard_centralizer_ne_top (J : HermitianForm 3 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) :
    centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ≠ ⊤ := by
  intro he
  exact zero_last_diagonal_not_centralizer J hJ h2 (coordinateCycle J hJ)
    (coordinateCycle_last_diagonal J hJ) (he ▸ mem_top _)

/-- An overgroup of the full block centralizer that moves the distinguished
line contains a matrix moving it to an orthogonal line. This is a geometric
orbit assertion, to be established over the finite quadratic field. -/
@[expose] def OrthogonalDisplacement (J : HermitianForm 3 F) (hJ : J.form = 1) : Prop :=
  ∀ M : Subgroup J.specialSubgroup,
    centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ≤ M →
    M ≠ centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) →
    ∃ g ∈ M, g.val.val 2 2 = 0

/-- The full stabilizers of two orthogonal nonisotropic lines generate SU₃.
The conjugation is the literal map `c ↦ g * c * g⁻¹`. -/
@[expose] def OrthogonalGeneration (J : HermitianForm 3 F) (hJ : J.form = 1) : Prop :=
  ∀ g : J.specialSubgroup, g.val.val 2 2 = 0 →
    centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup) ⊔
      (centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup)).map
        (MulAut.conj g).toMonoidHom = ⊤

/-- Two separate matrix claims imply maximality of the standard centralizer. -/
theorem standard_centralizer_isCoatom_of_orthogonal_geometry
    (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (hmove : OrthogonalDisplacement J hJ)
    (hgen : OrthogonalGeneration J hJ) :
    IsCoatom (centralizer ({SU3.standardInvolution J hJ} : Set J.specialSubgroup)) := by
  refine ⟨standard_centralizer_ne_top J hJ h2, ?_⟩
  intro M hM
  obtain ⟨g, hg, hg0⟩ := hmove M hM.le (ne_of_gt hM)
  apply top_unique
  rw [← hgen g hg0]
  refine sup_le hM.le ?_
  rintro _ ⟨c, hc, rfl⟩
  exact M.mul_mem (M.mul_mem hg (hM.le hc)) (M.inv_mem hg)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.Maximality
