module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.Stabilizer

/-!
# The plane determined by a unitary short root

The nilpotent part of the marked short root has image equal to the marked
isotropic plane. If a conjugate lies in the Hermitian radical, its image
lies in that plane. Four matrix entries of the intertwining equation show
that the conjugator preserves the plane. This transporter statement also
applies when the conjugator does not centralize the short root.

Source: the local common-centralizer step in Aschbacher–Smith F.4.42,
printed p.295 of `refs/quasithin.pdf`.
-/
open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortTransport
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
/-- A conjugator carrying the marked short root back into the Hermitian
radical preserves the original isotropic plane. -/
theorem conjugator_short_to_radical (g : SU F (form F σ hσ)) (X : hermitianMatrices F σ)
    (h : g * unipotentSU F σ hσ (shortParameter F σ) * g⁻¹ = unipotentSU F σ hσ X) :
    g ∈ planeParabolicSU F (form F σ hσ) := by
  have he := congrArg (fun a : SU F (form F σ hσ) => a.val.val)
    (mul_inv_eq_iff_eq_mul.mp h)
  change g.val.val * unipotentMatrix F (shortParameter F σ).val =
    unipotentMatrix F X.val * g.val.val at he
  have h20 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 2) he
  have h30 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 2) he
  have h21 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 3) he
  have h31 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 3) he
  simp [unipotentMatrix, shortParameter, mul_apply, Fin.sum_univ_succ] at h20 h30 h21 h31
  rw [mem_planeParabolicSU]
  exact ⟨h20,h30,h21,h31⟩

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortTransport
