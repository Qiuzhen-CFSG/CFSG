module

public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Concrete torus in the marked UnitaryThree Borel

Fixed-subfield units give diag(a,1,a⁻¹) in the Hermitian torus. The middle
entry excludes a projective scalar kernel. The domain is the fixed field,
not the quadratic matrix field.

These proofs adapt the corresponding `BorelReduction/HigherRankTori/UnitaryThree`
module in Chapter 15, using only the underlying matrix mathematics and no
later source assumptions. Their consumer is `MarkedModels.Cyclic`.
Source: Aschbacher--Smith, E.2.2, printed pp.215--216; the rank-one matrices
are those of Huppert II.10.12 and Huppert--Blackburn XI.3.1--3.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix
noncomputable section
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable {E : Type*} [Field E]

/-- The actual fixed subfield of the stored Hermitian conjugation. -/
abbrev unitaryFixedField (J : HermitianForm 3 E) : Subfield E :=
  FixedBy.subfield E J.conj

/-- Inclusion of fixed-subfield units into matrix-field units. -/
def unitaryFixedUnits (J : HermitianForm 3 E) : (unitaryFixedField J)ˣ →* Eˣ :=
  Units.map (unitaryFixedField J).subtype.toMonoidHom

private theorem unitaryFixedUnits_fixed (J : HermitianForm 3 E) (a : (unitaryFixedField J)ˣ) :
    J.conj (unitaryFixedUnits J a : E) = (unitaryFixedUnits J a : E) := a.val.property

/-- Inverse fixed units give the diagonal matrix diag(a, 1, a⁻¹). -/
theorem unitaryFixedTorus_matrix (J : HermitianForm 3 E) (a : (unitaryFixedField J)ˣ) :
    hermitianTorusMatrix J (unitaryFixedUnits J a⁻¹) =
      diagonal ![((a : unitaryFixedField J) : E), 1, (((a⁻¹ : (unitaryFixedField J)ˣ) : unitaryFixedField J) : E)] := by
  rw [hermitianTorusMatrix_eq, unitaryFixedUnits_fixed]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, unitaryFixedUnits]

/-- The concrete projective root–torus Borel. -/
abbrev psu3Borel (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range

/-- Fixed-field units in the actual projective root–torus Borel. -/
def psu3Torus (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (unitaryFixedField J)ˣ →* psu3Borel J hJ :=
  ((hermitianTorusPSU J hJ).comp ((unitaryFixedUnits J).comp invMonoidHom)).codRestrict _
    (fun a => Subgroup.mem_sup_right ⟨unitaryFixedUnits J a⁻¹, rfl⟩)

/-- The fixed middle entry makes the projective restriction faithful. -/
theorem psu3Torus_injective (J : HermitianForm 3 E)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (psu3Torus J hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hp : ProjGenLinGroup.mk (hermitianTorusGL J (unitaryFixedUnits J a⁻¹)) = 1 :=
    congrArg (fun x => x.val.val) ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨r, hr⟩ := hp
  have hm : (GeneralLinearGroup.scalar (Fin 3) r).val =
      diagonal ![((a : unitaryFixedField J) : E), 1,
        (((a⁻¹ : (unitaryFixedField J)ˣ) : unitaryFixedField J) : E)] := by
    rw [hr]
    exact unitaryFixedTorus_matrix J a
  have hr1 : (r : E) = 1 := by
    simpa using congrArg (fun x : Matrix (Fin 3) (Fin 3) E => x 1 1) hm
  apply Units.ext
  apply Subtype.ext
  have hh := congrArg (fun x : Matrix (Fin 3) (Fin 3) E => x 0 0) hm
  simpa [hr1] using hh.symm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
