module
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.LineMatrices
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order.Lines
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five.Model

/-!
# Faithfulness and coset counts for the projective Hermitian five-space

A central projective element commutes with the line radical. Since its
scalar covering kernel has order five and radical elements have fourth
power one, commutation lifts to SU. The checked radical commutant leaves
a scalar plus one rank-one nilpotent; a coordinate interchange eliminates
that nilpotent. This proves centerlessness without treating SU → PSU as
injective. The existing isotropic-line count descends through that same
scalar kernel to give the native projective point-coset count.

Source: Aschbacher–Smith F.4.3–6,13,24, printed pp.274–280,287;
the marked PSU₅(4) model is F.1.12(7), printed pp.263–264.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion
open RadicalCentralizers
open HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

/-- The actual projective five-dimensional carrier has trivial center. -/
theorem center_eq_bot (hc : Nat.card F = 16)
    (hσ : ∀ x, J.conj x = x^4) (hJ : J.form = 1) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨A,rfl⟩ := project_surjective J g
  have hcomm (B : J.specialSubgroup) (hB : B^4 = 1) : A*B = B*A :=
    commute_of_project_commute_fourth_power J hσ hc
      (mem_center_iff.mp hg (project J B)).symm hB
  obtain ⟨c,hc'⟩ := exists_trace_one J hσ hc
  obtain ⟨a,b,hab⟩ := line_matrix_shape J c hc' A.val.val (fun v => by
    have he := congrArg (fun C : J.specialSubgroup => C.val.val)
      (hcomm (LineCore.Parabolic.toSU J hJ v) (by
        rw [← map_pow, LineCore.Coord.fourth_power, map_one]))
    change A.val.val * (LineCore.Parabolic.ambientGL J v).val =
      (LineCore.Parabolic.ambientGL J v).val * A.val.val at he
    rwa [LineCore.Parabolic.ambientGL_val] at he)
  let s := Five.permutation J hJ (Equiv.swap 1 2)
  have hs : s^4 = 1 := by
    dsimp [s]
    rw [← map_pow]
    have ht : (Equiv.swap (1 : Fin 5) 2)^4 = 1 := by
      decide
    rw [ht, map_one]
  have he := congrArg (fun C : J.specialSubgroup => C.val.val 0 1) (hcomm s hs)
  change (A.val.val * s.val.val) 0 1 = (s.val.val * A.val.val) 0 1 at he
  rw [hab, show s.val.val = _ from Five.permutation_val J hJ _] at he
  have hb : b = 0 := by
    simpa [lineCentralMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.submatrix, Matrix.one_apply, Equiv.swap_inv, Equiv.swap_apply_def] using he.symm
  have ha : a ≠ 0 := by
    intro h
    have he : A.val.val = 0 := by
      rw [hab,h,hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineCentralMatrix]
    have hd := A.val.det_ne_zero
    simp [he] at hd
  let u := Units.mk0 a ha
  have hu : A.val = GeneralLinearGroup.scalar (Fin 5) u := by
    apply Units.ext
    rw [hab,hb,GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineCentralMatrix,Matrix.scalar,u]
  change project J A = 1
  apply Subtype.ext
  change ProjGenLinGroup.mk A.val = 1
  rw [hu]
  exact ProjGenLinGroup.mk_scalar u

/-- Inner automorphisms faithfully represent the projective carrier. -/
theorem conj_injective (hc : Nat.card F = 16)
    (hσ : ∀ x, J.conj x = x^4) (hJ : J.form = 1) :
    Function.Injective (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change MulAut.conj g = 1 at hg
  have hz : g ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [mem_center_iff]
    intro a
    have he := congrArg (fun f : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => f a) hg
    change g*a*g⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [center_eq_bot J hc hσ hJ] at hz

/-- The order-five scalar quotient preserves the native point-coset count. -/
theorem line_index (hc : Nat.card F = 16)
    (hσ : ∀ x, J.conj x = x^4) (hJ : J.form = 1) :
    (lineParabolic J).index = 17425 := by
  rw [lineParabolic, parabolic, Subgroup.index_map_eq _ (project_surjective J)
    (ker_project_le_specialStabilizer J _)]
  exact (Order.index_line_stabilizer J hc hσ hJ).trans (Order.card_isotropic_lines J hc hσ)

end Theory.SpecificGroups.UnitaryFive.SmallCompletion
