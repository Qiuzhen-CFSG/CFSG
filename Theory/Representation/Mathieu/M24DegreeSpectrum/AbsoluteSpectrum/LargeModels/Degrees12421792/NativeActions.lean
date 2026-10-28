module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Interface
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.CarrierMap

/-!
# Native realization from the presentation and matrix certificates

A finite bound on the explicit abstract presentation identifies its marked
surjection with the full Witt-design group. Independently, the seven positive
row-matrix equations produce a group homomorphism into matrices: the first
two equations supply inverses. Transpose then converts the row convention to
columns, and the matrix algebra equivalence gives the native linear action.

The two literal-data applications below retain the outstanding injectivity
and matrix-equation premises. They are not unconditional existence theorems.
The final native-action assembly must discharge those premises; density is
neither assumed nor needed here.

Sources: John Bray's ATLAS `M24G1-P1`; the four matrix files documented in
`Degrees12421792/source/README.md`; James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
open Sporadic.Mathieu NativeActions.Presentation

/-- Construct the actual native representation after the carrier and matrix certificates. -/
noncomputable def nativeOfRelations {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (hinj : Function.Injective toCarrier) (h : RowRelations A B) : NativeRealization A B := by
  let e : UniversalGroup ≃* M24 :=
    MulEquiv.ofBijective toCarrier ⟨hinj, toCarrier_surjective⟩
  let f : UniversalGroup →* Matrix (Fin d) (Fin d) (ZMod 2) :=
    toMonoid A.transpose B.transpose h.transpose
  let ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have ha : e.symm a = PresentedGroup.of 0 := by
    apply e.injective
    exact (e.apply_symm_apply a).trans toCarrier_zero.symm
  have hb : e.symm b = PresentedGroup.of 1 := by
    apply e.injective
    exact (e.apply_symm_apply b).trans toCarrier_one.symm
  refine ⟨ρ, ?_, ?_⟩
  · change LinearMap.toMatrix' (Matrix.toLinAlgEquiv' (f (e.symm a))) = _
    rw [ha, toMonoid_zero]
    exact LinearMap.toMatrix'_toLin' _
  · change LinearMap.toMatrix' (Matrix.toLinAlgEquiv' (f (e.symm b))) = _
    rw [hb, toMonoid_one]
    exact LinearMap.toMatrix'_toLin' _

/-- Literal degree-1242 consumer, with the two remaining certificates explicit. -/
noncomputable def native1242_of_relations
    (hinj : Function.Injective toCarrier)
    (h : RowRelations Data1242.first Data1242.second) :
    NativeRealization Data1242.first Data1242.second :=
  nativeOfRelations _ _ hinj h

/-- Literal degree-1792 consumer, with the two remaining certificates explicit. -/
noncomputable def native1792_of_relations
    (hinj : Function.Injective toCarrier)
    (h : RowRelations Data1792.first Data1792.second) :
    NativeRealization Data1792.first Data1792.second :=
  nativeOfRelations _ _ hinj h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
