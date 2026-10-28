module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Model
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Cubic

/-!
# Binary basis and global twists for the golden constituents

The two coefficients of each GoldenFour coordinate identify the domain with
six binary coordinates. A left inverse proves injectivity, and equality on
this basis proves all action identities. The scalar rule follows from the
τ identity by a general decomposition of every GoldenFour scalar.

The field twist is induced entrywise by the nontrivial field automorphism.
The dual twist is inverse-transpose; multiplicativity and involutivity are
proved for arbitrary SL₃ elements, without enumerating the group.

Source consumer: Aschbacher, *Sporadic Groups* (1994), 49.5, pp.283–284,
the natural and dual SL₃(4) constituents. The displayed matrices and integral
comparison retain John Bray and Gerald Höhn's ATLAS attribution and Research
and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation
namespace Golden
open Long.Block Long.Block.Realization

abbrev Six := Fin 3 × Fin 2

def coefficients : (Fin 3 → GoldenFour) ≃ₗ[Bit] (Six → Bit) where
  toFun v j := ![(v j.1).re, (v j.1).im] j.2
  invFun v i := ⟨v (i,0), v (i,1)⟩
  left_inv v := rfl
  right_inv v := by funext ⟨i,j⟩; fin_cases j <;> rfl
  map_add' v w := by funext ⟨i,j⟩; fin_cases j <;> rfl
  map_smul' a v := by funext ⟨i,j⟩; fin_cases j <;> rfl

def frobenius : GoldenFour ≃+* GoldenFour where
  toFun a := ⟨a.re + a.im, a.im⟩
  invFun a := ⟨a.re + a.im, a.im⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_mul' := by decide +kernel

def fieldTwist : SL(3,GoldenFour) ≃* SL(3,GoldenFour) where
  toFun := SpecialLinearGroup.map frobenius.toRingHom
  invFun := SpecialLinearGroup.map frobenius.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    funext i j
    exact frobenius.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    funext i j
    exact frobenius.apply_symm_apply _
  map_mul' := (SpecialLinearGroup.map frobenius.toRingHom).map_mul

theorem transpose_inv (g : SL(3,GoldenFour)) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
  apply Subtype.ext
  change g.val.adjugate.transpose = g.val.transpose.adjugate
  exact Matrix.adjugate_transpose g.val

def dualTwist : SL(3,GoldenFour) ≃* SL(3,GoldenFour) where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  invFun g := SpecialLinearGroup.transpose g⁻¹
  left_inv g := by
    change SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [← transpose_inv, inv_inv]
    rfl
  right_inv g := by
    change SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [← transpose_inv, inv_inv]
    rfl
  map_mul' g h := by
    rw [_root_.mul_inv_rev]
    apply Subtype.ext
    change (h⁻¹.val * g⁻¹.val).transpose = g⁻¹.val.transpose * h⁻¹.val.transpose
    exact Matrix.transpose_mul h⁻¹.val g⁻¹.val


def unitVector (j : Six) : Fin 3 → GoldenFour :=
  coefficients.symm (Pi.single j 1)

theorem ext_six {N : Type*} [AddCommMonoid N] [Module Bit N]
    (f g : (Fin 3 → GoldenFour) →ₗ[Bit] N)
    (h : ∀ j, f (unitVector j) = g (unitVector j)) : f = g := by
  apply ((Pi.basisFun Bit Six).map coefficients.symm).ext
  intro j
  simpa only [Module.Basis.map_apply, Pi.basisFun_apply, unitVector] using h j

def embedding (C : Matrix Index Six Bit) : (Fin 3 → GoldenFour) →ₗ[Bit] Binary :=
  C.mulVecLin.comp coefficients.toLinearMap

theorem embedding_injective (C : Matrix Index Six Bit) (L : Matrix Six Index Bit)
    (h : L * C = 1) : Function.Injective (embedding C) := by
  intro v w hvw
  apply coefficients.injective
  have hh := congrArg (fun x => L *ᵥ x) hvw
  change L *ᵥ (C *ᵥ coefficients v) = L *ᵥ (C *ᵥ coefficients w) at hh
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec,
    Matrix.one_mulVec] at hh
  exact hh

def goldenScale (a : GoldenFour) :
    (Fin 3 → GoldenFour) →ₗ[Bit] (Fin 3 → GoldenFour) :=
  (a • (LinearMap.id : (Fin 3 → GoldenFour) →ₗ[GoldenFour] (Fin 3 → GoldenFour))).restrictScalars Bit

def goldenAction (g : SL(3,GoldenFour)) :
    (Fin 3 → GoldenFour) →ₗ[Bit] (Fin 3 → GoldenFour) :=
  g.val.mulVecLin.restrictScalars Bit

theorem scalar_decomposition (a : GoldenFour) (v : Fin 3 → GoldenFour) :
    a • v = a.re • v + a.im • (goldenFourTau • v) := by
  funext i
  apply QuadraticAlgebra.ext <;>
    simp [goldenFourTau, QuadraticAlgebra.omega, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
  ring

theorem scalar_of_tau (e : (Fin 3 → GoldenFour) →ₗ[Bit] Binary) (opposite : Bool)
    (h : ∀ j, e (goldenFourTau • unitVector j) =
      orientationAction opposite (e (unitVector j))) (a : GoldenFour) (v) :
    e (a • v) = a.re • e v + a.im • orientationAction opposite (e v) := by
  have hh := ext_six (e.comp (goldenScale goldenFourTau))
    ((orientationAction opposite).comp e) h
  have hv := LinearMap.congr_fun hh v
  change e (goldenFourTau • v) = orientationAction opposite (e v) at hv
  rw [scalar_decomposition, map_add, map_smul, map_smul, hv]

theorem fixed_of_basis (e : (Fin 3 → GoldenFour) →ₗ[Bit] Binary)
    (hfixed : ∀ k j, (rightAxisTable k).map (Int.castRingHom Bit) *ᵥ
      e (unitVector j) = e (unitVector j)) (v) : AxisFixed (e v) := by
  intro k
  have h := ext_six (((rightAxisTable k).map (Int.castRingHom Bit)).mulVecLin.comp e)
    e (hfixed k)
  exact LinearMap.congr_fun h v

theorem cubic_of_basis (inverse opposite : Bool)
    (e : (Fin 3 → GoldenFour) →ₗ[Bit] Binary)
    (hcubic : ∀ j, (cubicTable inverse).map (Int.castRingHom Bit) *ᵥ
      e (unitVector j) = orientationAction opposite (e (unitVector j))) (v) :
    cubicAction inverse (e v) = orientationAction opposite (e v) := by
  change (cubicCoordinates inverse).map (Int.castRingHom Bit) *ᵥ e v = _
  rw [cubicCoordinates_eq_table]
  have h := ext_six (((cubicTable inverse).map (Int.castRingHom Bit)).mulVecLin.comp e)
    ((orientationAction opposite).comp e) hcubic
  exact LinearMap.congr_fun h v

theorem generator_of_basis (e : (Fin 3 → GoldenFour) →ₗ[Bit] Binary)
    (M : Matrix Index Index Bit) (g : SL(3,GoldenFour))
    (hg : ∀ j, M *ᵥ e (unitVector j) = e (g.val *ᵥ unitVector j)) (v) :
    M *ᵥ e v = e (g.val *ᵥ v) := by
  have h := ext_six (M.mulVecLin.comp e) (e.comp (goldenAction g)) hg
  exact LinearMap.congr_fun h v

theorem embedding_unitVector (C : Matrix Index Six Bit) (j : Six) :
    embedding C (unitVector j) = fun i => C i j := by
  change C *ᵥ coefficients (coefficients.symm (Pi.single j 1)) = _
  rw [coefficients.apply_symm_apply, Matrix.mulVec_single_one]
  rfl

end Golden
end ReferenceBlock.ModularCoordinates.FiniteCalculation
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
