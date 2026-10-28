module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Candidate

/-!
# Standard forms fixing the concrete projective Sylow subgroup

A linear/field/graph form fixing every `diagonal u` and `cycle` belongs to
`candidate`, the image of `model × C₂` acting by inner conjugation and the
graph–field involution. No coverage of the standard automorphism subgroup is
assumed here.

Multiplication by the graph–field involution removes the graph factor. In GL₃,
the commutator of `diag(1,u,u⁻¹)` and the cycle is the scalar `u⁻¹`. Since
central factors do not change a commutator, projective fixation forces the
remaining field automorphism to be trivial. A cyclic column shift then gives
a nonzero entry at (0,0). The three distinct diagonal eigenvalues force the
conjugating matrix to be diagonal, and the cycle equation makes it a scalar
multiple of `diag(1,v,v⁻¹)`. Undoing the shift proves candidate membership.

Source: the projective matrix calculation used in Aschbacher--Smith 15.3.38,
printed pp.1136--1137, manuscript of 1 March 2004. The passage from this
projective fixer to the central-cover centralizer remains with the consumer.
-/

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
noncomputable section
private abbrev GL3 := GeneralLinearGroup (Fin 3) F
private abbrev d (u : Fˣ) : GL3 := SpecialLinearGroup.toGL (diagonalSL u)
private abbrev r : GL3 := SpecialLinearGroup.toGL cycleSL
private abbrev s (u : Fˣ) : GL3 := GeneralLinearGroup.scalar (Fin 3) u

private theorem scalar_inj : Function.Injective s := by
  intro u v h
  apply Units.ext
  exact congrArg (fun A : GL3 => A.val 0 0) h

private theorem conj_scalar (A : GL3) (u : Fˣ) : MulAut.conj A (s u) = s u := by
  change A * s u * A⁻¹ = s u
  rw [← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem comm_scalar_mul (u v : Fˣ) (A B : GL3) :
    ⁅s u * A, s v * B⁆ = ⁅A, B⁆ := by
  have hc (w : Fˣ) (C : GL3) : Commute (s w) C :=
    GeneralLinearGroup.scalar_commute w C
  rw [commutatorElement_mul_left_eq_conj_mul, (hc u _).commutator_eq, mul_one,
    (hc u _).eq, mul_inv_cancel_right,
    commutatorElement_mul_right_eq_mul_conj, (hc v A).symm.commutator_eq,
    one_mul, (hc v _).eq, mul_inv_cancel_right]

private theorem diagonal_cycle_relation (u : Fˣ) : d u * r = s (u⁻¹) * (r * d u) := by
  apply Units.ext
  have hi : (↑u⁻¹ : F) * (↑u⁻¹ : F) = (u : F) := by
    have h := congrArg Units.val (unit_inv u⁻¹)
    simpa [pow_two] using h.symm
  change !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] * !![0,1,0;0,0,1;1,0,0] =
    Matrix.scalar (Fin 3) (↑u⁻¹ : F) *
      (!![0,1,0;0,0,1;1,0,0] * !![1,0,0;0,(u : F),0;0,0,↑u⁻¹])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  simpa only [Units.val_inv_eq_inv_val] using hi.symm

private theorem diagonal_cycle_commutator (u : Fˣ) : ⁅d u, r⁆ = s (u⁻¹) := by
  rw [commutatorElement_def, diagonal_cycle_relation]
  group

private theorem field_diagonal (σ : F ≃+* F) (u : Fˣ) :
    SpecialLinearGroup.map σ.toRingHom (diagonalSL u) =
      diagonalSL (Units.map σ.toMonoidHom u) := by
  apply Subtype.ext
  ext i j
  change σ ((!![1,0,0;0,(u : F),0;0,0,(↑u⁻¹ : F)] : Matrix (Fin 3) (Fin 3) F) i j) =
    (!![1,0,0;0,σ (u : F),0;0,0,σ (↑u⁻¹ : F)] : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem field_cycle (σ : F ≃+* F) :
    SpecialLinearGroup.map σ.toRingHom cycleSL = cycleSL := by
  apply Subtype.ext
  ext i j
  change σ ((!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) i j) =
    (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem lift_fix (A : GL3) (X Y : SL)
    (h : PSL3.OuterSolvable.linearConj F A (project X) = project Y) :
    ∃ u : Fˣ, MulAut.conj A (SpecialLinearGroup.toGL X) =
      s u * SpecialLinearGroup.toGL Y := by
  obtain ⟨u, hu, he⟩ := (project_eq_iff _ _).mp h
  have hu0 : u ≠ 0 := by intro h0; simp [h0] at hu
  refine ⟨Units.mk0 u hu0, ?_⟩
  rw [MulAut.conj_apply, ← PSL3.OuterSolvable.linearConjSL_toGL]
  exact Units.ext he

private theorem field_project (σ : F ≃+* F) (X : SL) :
    PSL3.OuterSolvable.fieldAction F σ (project X) =
      project (SpecialLinearGroup.map σ.toRingHom X) :=
  PSL3.OuterSolvable.fieldAction_mk F σ X

private theorem field_eq_one_of_fixing (A : GL3) (σ : F ≃+* F)
    (hd : ∀ u : Fˣ, (PSL3.OuterSolvable.linearConj F A *
      PSL3.OuterSolvable.fieldAction F σ) (diagonal u) = diagonal u)
    (hr : (PSL3.OuterSolvable.linearConj F A *
      PSL3.OuterSolvable.fieldAction F σ) cycle = cycle) : σ = 1 := by
  have hd' (u : Fˣ) : PSL3.OuterSolvable.linearConj F A
      (project (diagonalSL (Units.map σ.toMonoidHom u))) = project (diagonalSL u) := by
    have h := hd u
    change PSL3.OuterSolvable.linearConj F A
      (PSL3.OuterSolvable.fieldAction F σ (project (diagonalSL u))) = _ at h
    rw [field_project, field_diagonal] at h
    exact h
  have hr' : PSL3.OuterSolvable.linearConj F A (project cycleSL) = project cycleSL := by
    change PSL3.OuterSolvable.linearConj F A
      (PSL3.OuterSolvable.fieldAction F σ (project cycleSL)) = _ at hr
    rw [field_project, field_cycle] at hr
    exact hr
  obtain ⟨w, hw⟩ := lift_fix A cycleSL cycleSL hr'
  have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
    obtain ⟨v, hv⟩ := lift_fix A _ _ (hd' u)
    have h := congrArg (MulAut.conj A)
      (diagonal_cycle_commutator (Units.map σ.toMonoidHom u))
    rw [map_commutatorElement, hv, hw, comm_scalar_mul,
      diagonal_cycle_commutator, conj_scalar] at h
    exact inv_injective (scalar_inj h.symm)
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · exact congrArg Units.val (hu (Units.mk0 x hx))

private theorem exists_distinct_diagonal : ∃ u : Fˣ,
    Function.Injective (fun i : Fin 3 => (![1, (u : F), (↑u⁻¹ : F)]) i) := by
  obtain ⟨a, ha⟩ := exists_fieldFrobenius_ne
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha
  let u := Units.mk0 a ha0
  have hu1 : (u : F) ≠ 1 := ha1
  have hi1 : (↑u⁻¹ : F) ≠ 1 := by simpa using hu1
  have hia : (↑u⁻¹ : F) ≠ (u : F) := by
    rw [unit_inv]
    exact ha
  refine ⟨u, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hu1 hij.symm).elim
  · exact (hi1 hij.symm).elim
  · exact (hu1 hij).elim
  · rfl
  · exact (hia hij.symm).elim
  · exact (hi1 hij).elim
  · exact (hia hij).elim
  · rfl

private theorem linear_scalar (u : Fˣ) : PSL3.OuterSolvable.linearConj F (s u) = 1 := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H X =>
    rw [PSL3.OuterSolvable.linearConj_mk]
    have h : PSL3.OuterSolvable.linearConjSL F (s u) X = X := by
      apply SpecialLinearGroup.toGL_injective
      rw [PSL3.OuterSolvable.linearConjSL_toGL,
        GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
    rw [h]
    rfl

private theorem inner_mem_candidate (x : PSL) (hx : x ∈ model) : MulAut.conj x ∈ candidate := by
  refine ⟨(⟨x, hx⟩, 1), ?_⟩
  change modelInner ⟨x, hx⟩ * involutionHom graphField graphField_sq 1 = MulAut.conj x
  rw [map_one, mul_one]
  rfl

private theorem linear_diagonal_mem (u : Fˣ) : PSL3.OuterSolvable.linearConj F (d u) ∈ candidate := by
  rw [PSL3.OuterSolvable.linearConj_toGL]
  exact inner_mem_candidate (diagonal u) (diagonal_mem_model u)

private theorem linear_cycle_mem : PSL3.OuterSolvable.linearConj F r ∈ candidate := by
  rw [PSL3.OuterSolvable.linearConj_toGL]
  exact inner_mem_candidate cycle cycle_mem_model

-- A nonzero entry at (0,0) fixes the scalar in the diagonal equation.
private theorem linear_origin (A : GL3) (h00 : A.val 0 0 ≠ 0)
    (hd : ∀ u : Fˣ, PSL3.OuterSolvable.linearConj F A (diagonal u) = diagonal u)
    (hr : PSL3.OuterSolvable.linearConj F A cycle = cycle) :
    PSL3.OuterSolvable.linearConj F A ∈ candidate := by
  obtain ⟨u, hu⟩ := exists_distinct_diagonal
  let e : Fin 3 → F := ![1, (u : F), (↑u⁻¹ : F)]
  obtain ⟨v, hv⟩ := lift_fix A (diagonalSL u) (diagonalSL u) (hd u)
  have hm : A * d u = s v * d u * A := (mul_inv_eq_iff_eq_mul).mp hv
  have hm' : A.val * !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] =
      Matrix.scalar (Fin 3) (v : F) * !![1,0,0;0,(u : F),0;0,0,↑u⁻¹] * A.val :=
    congrArg Units.val hm
  have he (i j : Fin 3) : A.val i j * e j = (v : F) * (e i * A.val i j) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hm'
    fin_cases i <;> fin_cases j <;>
      simpa [e, Matrix.mul_apply, Fin.sum_univ_three, mul_assoc] using h
  have hv1 : (v : F) = 1 := mul_right_cancel₀ h00 (by simpa [e] using (he 0 0).symm)
  have hoff (i j : Fin 3) (hij : i ≠ j) : A.val i j = 0 := by
    have h := he i j
    rw [hv1, one_mul, mul_comm (e i)] at h
    exact (mul_eq_mul_left_iff.mp h).resolve_left (fun h => hij (hu h.symm))
  obtain ⟨w, hw⟩ := lift_fix A cycleSL cycleSL hr
  have hR : A * r = s w * r * A := (mul_inv_eq_iff_eq_mul).mp hw
  have hR' : A.val * !![0,1,0;0,0,1;1,0,0] =
      Matrix.scalar (Fin 3) (w : F) * !![0,1,0;0,0,1;1,0,0] * A.val :=
    congrArg Units.val hR
  have h01 : A.val 0 0 = (w : F) * A.val 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hR'
  have h20 : A.val 2 2 = (w : F) * A.val 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 0) hR'
  have h11 : A.val 1 1 = (↑w⁻¹ : F) * A.val 0 0 := by
    rw [h01, ← mul_assoc, Units.inv_mul, one_mul]
  have hA : A = s (Units.mk0 (A.val 0 0) h00) * d (w⁻¹) := by
    apply Units.ext
    change A.val = Matrix.scalar (Fin 3) (A.val 0 0) *
      !![1,0,0;0,(↑w⁻¹ : F),0;0,0,(↑(w⁻¹)⁻¹ : F)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hoff, h11, h20, mul_comm]
  rw [hA, map_mul, linear_scalar, one_mul]
  exact linear_diagonal_mem _

private theorem linear_fixing (A : GL3)
    (hd : ∀ u : Fˣ, PSL3.OuterSolvable.linearConj F A (diagonal u) = diagonal u)
    (hr : PSL3.OuterSolvable.linearConj F A cycle = cycle) :
    PSL3.OuterSolvable.linearConj F A ∈ candidate := by
  have hrot (k : ℕ) : PSL3.OuterSolvable.linearConj F (r ^ k) ∈ candidate := by
    rw [map_pow]
    exact candidate.pow_mem linear_cycle_mem k
  have hfix (k : ℕ) (x : PSL) (hx : x ∈ model) :
      PSL3.OuterSolvable.linearConj F (r ^ k) x = x :=
    candidate_fixes_model (hrot k) ⟨x, hx⟩
  have hmove (k : ℕ) (hk : (A * r ^ k).val 0 0 ≠ 0) :
      PSL3.OuterSolvable.linearConj F A ∈ candidate := by
    have hd' (u : Fˣ) :
        PSL3.OuterSolvable.linearConj F (A * r ^ k) (diagonal u) = diagonal u := by
      rw [map_mul, MulAut.mul_apply,
        hfix k (diagonal u) (diagonal_mem_model u), hd]
    have hr' : PSL3.OuterSolvable.linearConj F (A * r ^ k) cycle = cycle := by
      rw [map_mul, MulAut.mul_apply,
        hfix k cycle cycle_mem_model, hr]
    have h := linear_origin (A * r ^ k) hk hd' hr'
    rw [map_mul] at h
    have hh := candidate.mul_mem h (candidate.inv_mem (hrot k))
    simpa only [mul_inv_cancel_right] using hh
  by_cases h0 : A.val 0 0 = 0
  · by_cases h2 : A.val 0 2 = 0
    · have h1 : A.val 0 1 ≠ 0 := by
        intro h1
        apply GeneralLinearGroup.det_ne_zero A
        simp [Matrix.det_fin_three, h0, h1, h2]
      apply hmove 2
      change (A.val * (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F)^2) 0 0 ≠ 0
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_three] using h1
    · apply hmove 1
      change (A.val * (!![0,1,0;0,0,1;1,0,0] : Matrix (Fin 3) (Fin 3) F)^1) 0 0 ≠ 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using h2
  · exact linear_origin A h0 hd hr

private theorem semilinear_fixing (A : GL3) (σ : F ≃+* F)
    (hd : ∀ u : Fˣ, (PSL3.OuterSolvable.linearConj F A *
      PSL3.OuterSolvable.fieldAction F σ) (diagonal u) = diagonal u)
    (hr : (PSL3.OuterSolvable.linearConj F A *
      PSL3.OuterSolvable.fieldAction F σ) cycle = cycle) :
    PSL3.OuterSolvable.linearConj F A * PSL3.OuterSolvable.fieldAction F σ ∈ candidate := by
  have hσ := field_eq_one_of_fixing A σ hd hr
  subst σ
  simp only [map_one, mul_one] at hd hr ⊢
  exact linear_fixing A hd hr

private theorem graphField_mem_candidate : graphField ∈ candidate := by
  refine ⟨(1, Multiplicative.ofAdd (1 : ZMod 2)), ?_⟩
  change modelInner 1 * involutionHom graphField graphField_sq
    (Multiplicative.ofAdd (1 : ZMod 2)) = graphField
  rw [map_one, one_mul, involutionHom_generator]

/-- Every explicit standard form fixing the diagonal factor and cycle lies in the
concrete inner/graph–field candidate, with no further mathematical premises. -/
public theorem standardForm_mem_candidate_of_fixes
    (A : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F) (t : C2)
    (hd : ∀ u : Fˣ, standardForm A σ t (diagonal u) = diagonal u)
    (hr : standardForm A σ t cycle = cycle) : standardForm A σ t ∈ candidate := by
  have ht : t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) := by
    change t.toAdd = (0 : ZMod 2) ∨ t.toAdd = 1
    change ZMod 2 at t
    fin_cases t <;> decide
  rcases ht with rfl | rfl
  · simp only [standardForm, map_one, mul_one] at hd hr ⊢
    exact semilinear_fixing A σ hd hr
  · have he : standardForm A σ (Multiplicative.ofAdd (1 : ZMod 2)) * graphField =
        PSL3.OuterSolvable.linearConj F A *
          PSL3.OuterSolvable.fieldAction F (σ * fieldFrobenius) := by
      rw [standardForm, involutionHom_generator, map_mul, ← frobenius_eq_fieldAction,
        graphField, ← mul_assoc, mul_assoc
          (PSL3.OuterSolvable.linearConj F A * PSL3.OuterSolvable.fieldAction F σ),
        ← pow_two, PSL3.OuterSolvable.graph_sq, mul_one]
      simp only [mul_assoc]
    have hd' (u : Fˣ) : (PSL3.OuterSolvable.linearConj F A *
        PSL3.OuterSolvable.fieldAction F (σ * fieldFrobenius)) (diagonal u) = diagonal u := by
      rw [← he, MulAut.mul_apply, graphField_diagonal, hd]
    have hr' : (PSL3.OuterSolvable.linearConj F A *
        PSL3.OuterSolvable.fieldAction F (σ * fieldFrobenius)) cycle = cycle := by
      rw [← he, MulAut.mul_apply, graphField_cycle, hr]
    have h := semilinear_fixing A (σ * fieldFrobenius) hd' hr'
    rw [← he] at h
    have hh := candidate.mul_mem h (candidate.inv_mem graphField_mem_candidate)
    simpa only [mul_inv_cancel_right] using hh

end
end Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
