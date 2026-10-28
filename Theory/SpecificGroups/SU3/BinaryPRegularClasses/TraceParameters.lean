module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.SpecificGroups.SL3.PRegularClasses.GLIntertwiner

/-!
# Trace parameters for special unitary three-space

For every nondegenerate Hermitian form, the inverse trace of a unitary matrix
is the field conjugate of its trace. Thus the trace determines the characteristic
polynomial in SU₃. For odd-order elements in characteristic two, the existing
SL₃ semisimplicity and descent results supply an invertible linear intertwiner.
This does not yet assert conjugacy in SU₃: the intertwiner still needs its
unitary and determinant corrections.

The determinant of every unitary matrix has norm one, with no normalization
of the Gram matrix. The proofs cancel the invertible Gram matrix explicitly.
Source context: GLS III, 2.8.2 and 2.8.6(a), with the SU₃ family of 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses
variable {F : Type*} [Field F]

private def toSL (J : HermitianForm 3 F) :
    J.specialSubgroup →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun g := ⟨g.val.val, congrArg Units.val
    ((J.mem_specialSubgroup_iff g.val).mp g.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem toSL_injective (J : HermitianForm 3 F) :
    Function.Injective (toSL J) := by
  intro g h he
  exact Subtype.ext (Units.ext (congrArg Subtype.val he))

/-- The inverse trace of a unitary matrix is the conjugate trace, for the original Gram matrix. -/
public theorem trace_inv (J : HermitianForm 3 F) (g : J.unitarySubgroup) :
    (g⁻¹).val.val.trace = J.conj g.val.val.trace := by
  have hg := (J.mem_unitarySubgroup_iff g.val).mp g.property
  have hf : IsUnit J.form :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr J.form_nondegenerate)
  have hrel : J.conjTranspose g.val.val * J.form = J.form * (g.val⁻¹).val := by
    calc
      _ = (J.conjTranspose g.val.val * J.form * g.val.val) * (g.val⁻¹).val := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hg]
  have he : J.form⁻¹ * J.conjTranspose g.val.val * J.form = (g.val⁻¹).val := by
    rw [mul_assoc, hrel, ← mul_assoc, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr J.form_nondegenerate), one_mul]
  change (g.val⁻¹).val.trace = _
  rw [← he, Matrix.trace_conj' hf]
  change (g.val.val.map J.conj).transpose.trace = _
  rw [Matrix.trace_transpose]
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

/-- The determinant of a unitary matrix has norm one for every nondegenerate Gram matrix. -/
public theorem det_norm (J : HermitianForm 3 F) (g : J.unitarySubgroup) :
    J.conj g.val.val.det * g.val.val.det = 1 := by
  have hd := congrArg Matrix.det ((J.mem_unitarySubgroup_iff g.val).mp g.property)
  change ((g.val.val.map J.conj).transpose * J.form * g.val.val).det = J.form.det at hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  change (J.conj.mapMatrix g.val.val).det * J.form.det * g.val.val.det = J.form.det at hd
  rw [← J.conj.map_det] at hd
  apply mul_right_cancel₀ J.form_nondegenerate
  simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using hd

/-- A single trace determines the characteristic polynomial of a special unitary three-space matrix. -/
public theorem charpoly_eq_of_trace_eq (J : HermitianForm 3 F) (g h : J.specialSubgroup)
    (ht : g.val.val.trace = h.val.val.trace) :
    g.val.val.charpoly = h.val.val.charpoly := by
  apply SL3.PRegularClasses.charpoly_eq_of_trace_eq (toSL J g) (toSL J h) ht
  have hgi := trace_inv J ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩
  have hhi := trace_inv J ⟨h.val, J.specialSubgroup_le_unitarySubgroup h.property⟩
  change (g.val⁻¹).val.trace = _ at hgi
  change (h.val⁻¹).val.trace = _ at hhi
  have he : (toSL J g)⁻¹ = toSL J g⁻¹ := (map_inv (toSL J) g).symm
  rw [he, show (toSL J h)⁻¹ = toSL J h⁻¹ from (map_inv (toSL J) h).symm]
  change (g.val⁻¹).val.trace = (h.val⁻¹).val.trace
  rw [hgi, hhi, ht]

/-- Odd order gives semisimplicity of the literal natural special unitary action. -/
public theorem isSemisimple_of_pRegular [CharP F 2]
    (J : HermitianForm 3 F) (g : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g) :
    Module.End.IsSemisimple (Matrix.toLin' g.val.val) := by
  apply SL3.PRegularClasses.isSemisimple_of_pRegular (toSL J g)
  rwa [orderOf_injective (toSL J) (toSL_injective J)]

/-- Odd-order special unitary elements with equal trace have a linear intertwiner over the original field. -/
public theorem exists_GL_intertwiner_of_trace_eq [CharP F 2]
    (J : HermitianForm 3 F) (g h : J.specialSubgroup)
    (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (ht : g.val.val.trace = h.val.val.trace) :
    ∃ D : GL (Fin 3) F, D * g.val = h.val * D := by
  have hgo : ¬ 2 ∣ orderOf (toSL J g) := by
    rwa [orderOf_injective (toSL J) (toSL_injective J)]
  have hho : ¬ 2 ∣ orderOf (toSL J h) := by
    rwa [orderOf_injective (toSL J) (toSL_injective J)]
  obtain ⟨D, ⟨d, rfl⟩, hd⟩ :=
    SL3.PRegularClasses.exists_unit_intertwiner_of_charpoly_eq
      (toSL J g) (toSL J h) hgo hho (charpoly_eq_of_trace_eq J g h ht)
  exact ⟨d, Units.ext hd⟩
end Theory.SpecificGroups.SU3.BinaryPRegularClasses
