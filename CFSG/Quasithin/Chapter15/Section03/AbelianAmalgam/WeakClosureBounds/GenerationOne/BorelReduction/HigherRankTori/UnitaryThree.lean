module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# Fixed-field units in the projective unitary Borel

The matrix field E has order q²; its Hermitian fixed subfield has order q.
Restricting Huppert's torus to inverses of fixed units gives diag(a, 1, a⁻¹).
The middle entry excludes a nonidentity scalar kernel in the actual
projection to PSU₃. The image lies in the concrete root–torus Borel.
The existing matrix-basis and Sylow conjugation equivalences transport
this injection to every source-form Sylow normalizer.

Source: Aschbacher–Smith, E.2.2, printed pp.215–216, and 15.3.65, printed
p.1152 (`refs/quasithin.pdf`, combined manuscript of 1 March 2004).
The torus matrices and form transport come from Huppert II.10.12 and II.10.4.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped Matrix
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
variable {E : Type*} [Field E]

/-- The actual fixed subfield of the stored Hermitian conjugation. -/
abbrev unitaryFixedField (J : HermitianForm 3 E) : Subfield E :=
  FixedBy.subfield E J.conj

/-- The source parameter counts fixed elements, not matrix-field elements. -/
theorem unitaryFixedField_card [Finite E] (J : HermitianForm 3 E)
    (f : ℕ) (hf : 0 < f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    Nat.card (unitaryFixedField J) = 2 ^ f :=
  fixed_card J f hf hcard hconj

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

/-- The injection for any source Hermitian form and any Sylow 2-subgroup,
transported by the genuine basis change and inner conjugation. -/
theorem exists_psu3SylowTorus [Finite E] (J : HermitianForm 3 E)
    (f : ℕ) (hf : 0 < f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ t : (unitaryFixedField J)ˣ →*
      Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      Function.Injective t := by
  obtain ⟨C, hC, g, hB⟩ := psu_sylow_normalizer_eq_matrix_borel J f hf hcard hconj T
  let e := FormTransport.projectiveEquiv J C hC
  let B := psu3Borel (FormTransport.standardForm J) rfl
  let t₀ : (unitaryFixedField J)ˣ →* B := psu3Torus (FormTransport.standardForm J) rfl
  let t := e.symm.toMonoidHom.comp
    ((MulAut.conj g).toMonoidHom.comp (B.subtype.comp t₀))
  have ht : Function.Injective t := e.symm.injective.comp
    ((MulAut.conj g).injective.comp
      (Subtype.val_injective.comp (psu3Torus_injective (FormTransport.standardForm J) rfl)))
  have hmem (a : (unitaryFixedField J)ˣ) :
      t a ∈ Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [hB]
    change e (e.symm ((MulAut.conj g) (t₀ a))) ∈ B.map (MulAut.conj g).toMonoidHom
    rw [e.apply_symm_apply]
    exact Subgroup.mem_map_of_mem _ (t₀ a).property
  exact ⟨t.codRestrict _ hmem, fun _ _ h => ht (congrArg Subtype.val h)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
