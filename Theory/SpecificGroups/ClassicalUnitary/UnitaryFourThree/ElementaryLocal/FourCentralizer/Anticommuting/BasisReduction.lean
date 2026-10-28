module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Lifts
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport

/-!
# Anticommuting lifts and the two-plus-two eigenbasis

Conjugating the first lift by the second negates it, so its trace vanishes
in characteristic three. The scalar-kernel calculation then rescales it
to a linear involution. A supplied two-plus-two eigenbasis forces the
rescaling scalar to have fourth power one by taking determinants; hence
the rescaled matrix remains special unitary. A supplied Hermitian basis
normalization produces an actual full-unitary conjugator.

The two eigenbasis existence statements remain explicit inputs. Their
owners are the linear and unitary eigenbasis modules under
`TwoLocal.InvolutionTransport`; no projective-involution trace theorem is
used here. This reduction needs no hypothesis on the square of the second
lift.

Sources: GLS3 chapter 2, §2.3, for the scalar and unitary conventions;
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 and repeated on p.482 of
`refs/quasithin.pdf`, for the centralizer application.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting

/-- Anticommutation by an invertible matrix forces trace zero in characteristic three. -/
theorem trace_eq_zero (a b : SU)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val)) :
    Matrix.trace a.val.val = 0 := by
  have hconj : b.val.val * a.val.val * (b.val⁻¹).val = -a.val.val := by
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) FiniteField.Nine =>
      M * (b.val⁻¹).val) hab
    simp only [mul_assoc, Units.mul_inv, mul_one, neg_mul] at he
    simpa only [neg_neg, mul_assoc] using (congrArg Neg.neg he).symm
  have ht := congrArg Matrix.trace hconj
  rw [Matrix.trace_units_conj, Matrix.trace_neg] at ht
  have h2 : (2 : FiniteField.Nine) * Matrix.trace a.val.val = 0 := by
    calc
      _ = Matrix.trace a.val.val + Matrix.trace a.val.val := two_mul _
      _ = -Matrix.trace a.val.val + Matrix.trace a.val.val :=
        congrArg (fun x => x + Matrix.trace a.val.val) ht
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

/-- The existing linear and Hermitian eigenbasis contracts produce a genuine
unitary conjugator after rescaling the first anticommuting lift. -/
theorem exists_scaled_unitary_conjugator_of_eigenbasis_inputs
    (hlinear : ∀ M : GL (Fin 4) FiniteField.Nine, M ^ 2 = 1 → Matrix.trace M.val = 0 →
      ∃ P : GL (Fin 4) FiniteField.Nine,
        P * standardInvolutionGL * P⁻¹ = M)
    (hnormalize : ∀ (A : SU) (P : GL (Fin 4) FiniteField.Nine),
      P * standardInvolutionGL * P⁻¹ = A.val →
        ∃ C : (form 4).unitarySubgroup,
          C.val * standardInvolutionGL * C.val⁻¹ = A.val)
    (a b : SU) (ha : (project 4 a) ^ 2 = 1)
    (hab : a.val.val * b.val.val = -(b.val.val * a.val.val)) :
    ∃ (u : FiniteField.Nineˣ) (C : (form 4).unitarySubgroup),
      u ^ 4 = 1 ∧
      C.val * standardInvolutionGL * C.val⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * a.val := by
  obtain ⟨u, hu⟩ := exists_involutive_scalar_multiple a ha
  let M := GeneralLinearGroup.scalar (Fin 4) u * a.val
  have hMt : Matrix.trace M.val = 0 := by
    change Matrix.trace (Matrix.scalar (Fin 4) u.val * a.val.val) = 0
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul,
      trace_eq_zero a b hab, smul_zero]
  obtain ⟨P, hP⟩ := hlinear M hu hMt
  have had : GeneralLinearGroup.det a.val = 1 :=
    ((form 4).mem_specialSubgroup_iff a.val).mp a.property |>.2
  have hDd : GeneralLinearGroup.det standardInvolutionGL = 1 :=
    ((form 4).mem_specialSubgroup_iff standardInvolutionGL).mp standardInvolutionSU.property |>.2
  have hu4 : u ^ 4 = 1 := by
    have hd := congrArg GeneralLinearGroup.det hP
    simpa only [M, map_mul, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      had, hDd, mul_one, mul_inv_cancel] using hd.symm
  have hscalar : GeneralLinearGroup.scalar (Fin 4) u ∈ (form 4).specialSubgroup :=
    (IsotropicStabilizers.scalar_mem_specialSubgroup_iff (form 4) (form_conj_cube 4) u).mpr hu4
  let A : SU := ⟨M, (form 4).specialSubgroup.mul_mem hscalar a.property⟩
  obtain ⟨C, hC⟩ := hnormalize A P hP
  exact ⟨u, C, hu4, hC⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Anticommuting
