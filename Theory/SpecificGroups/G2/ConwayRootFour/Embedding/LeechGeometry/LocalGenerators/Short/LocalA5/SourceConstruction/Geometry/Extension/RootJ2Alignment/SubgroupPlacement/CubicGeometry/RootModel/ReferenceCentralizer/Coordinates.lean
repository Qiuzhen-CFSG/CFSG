module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Eigenspaces
public import Mathlib.LinearAlgebra.Determinant

/-!
# Three-dimensional coordinates for the full reference common centralizer

The chosen eigenspace is literally the U-fixed vectors on which the reference
cubic and the actual scalar Y agree. This identifies its action kernel using
binary Leech vectors, then identifies faithfulness with a sufficient kernel
calculation in the original integral group modulo its two central signs.

Add trivial coordinates to reach dimension three, and write the actual action
in a basis. The dimension bound is proved in `Eigenspaces`; an exact dimension
calculation is unnecessary. Padding preserves the determinant and preserves
faithfulness. Thus a determinant-one proof constructs a homomorphism to SL₃(4),
and a proof of the integral sign kernel makes that homomorphism injective.
Neither of those two geometric assertions is assumed to be a source theorem.
`ReferenceCentralizer.Application` supplies the marked-root consumers.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5, p.283.
The actual icosian and Leech quotient actions retain the ATLAS attribution
and central-sign conventions of the imported modules.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

/-- The chosen field generator acts by the literal tetrahedral element Y. -/
theorem referenceScalar_smul (v : fixedSpace) :
    (referenceScalar • v).val = quotientModTwoRepresentation y v.val := by
  rw [Long.smul_val]
  simp [referenceScalar, Atlas.Algebra.goldenFourTau, QuadraticAlgebra.omega]

/-- The chosen eigenspace has a description using only the original binary action. -/
theorem mem_referenceEigenspace_scalar_iff (v : fixedSpace) :
    v ∈ referenceEigenspace referenceScalar ↔
      quotientModTwoRepresentation referenceCubic v.val =
        quotientModTwoRepresentation y v.val := by
  rw [mem_referenceEigenspace, Subtype.ext_iff]
  rw [referenceScalar_smul]
  rfl

/-- The kernel test involves precisely the U-fixed vectors with equal cubic and Y images. -/
theorem referenceEigenAction_eq_one_iff (g : referenceCentralizer) :
    referenceEigenAction referenceScalar g = 1 ↔
      ∀ v ∈ fixedSpace,
        quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
          quotientModTwoRepresentation g.val v = v := by
  constructor
  · intro h v hv he
    let w : referenceEigenspace referenceScalar :=
      ⟨⟨v, hv⟩, (mem_referenceEigenspace_scalar_iff ⟨v,hv⟩).mpr he⟩
    exact congrArg (fun f : referenceEigenspace referenceScalar ≃ₗ[F]
        referenceEigenspace referenceScalar => (f w).val.val) h
  · intro h
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    exact h v.val.val v.val.property ((mem_referenceEigenspace_scalar_iff v.val).mp v.property)

/-- The two-sign quotient turns the integral kernel calculation into faithfulness. -/
theorem referenceEigenAction_injective_of_lift_kernel
    (hk : ∀ g : LeechIsometryGroup, leechCentralProjection g ∈ referenceCentralizer →
      (∀ v ∈ fixedSpace,
        quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
          leechModTwoRepresentation g v = v) → g ∈ leechCentralSigns) :
    Function.Injective (referenceEigenAction referenceScalar) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  obtain ⟨k, he⟩ := leechCentralProjection_surjective g.val
  have hf := (referenceEigenAction_eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)
  have hs : k ∈ leechCentralSigns := hk k (he.symm ▸ g.property) (by
    intro v hv hc
    rw [← quotientModTwoRepresentation_compatible, he]
    exact hf v hv hc)
  apply Subtype.ext
  change g.val = 1
  rw [← he]
  apply MonoidHom.mem_ker.mp
  rwa [leechCentralProjection_kernel]

abbrev ReferenceNatural := referenceEigenspace referenceScalar

abbrev ReferencePadding := Fin (3 - Module.finrank F ReferenceNatural) → F

abbrev ReferencePadded := ReferenceNatural × ReferencePadding

/-- Trivial padding reaches dimension three using only the proved upper bound. -/
theorem referencePadded_finrank : Module.finrank F ReferencePadded = 3 := by
  rw [Module.finrank_prod]
  simp only [ReferencePadding, Module.finrank_pi, Fintype.card_fin]
  exact Nat.add_sub_of_le referenceEigenspace_finrank_le_three

/-- The intrinsic action extended by the identity on the missing coordinates. -/
def referencePaddedAction : referenceCentralizer →* (ReferencePadded ≃ₗ[F] ReferencePadded) where
  toFun g := (referenceEigenAction referenceScalar g).prodCongr (LinearEquiv.refl F ReferencePadding)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact Prod.ext (DFunLike.congr_fun (map_one (referenceEigenAction referenceScalar)) v.1) rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact Prod.ext (DFunLike.congr_fun (map_mul (referenceEigenAction referenceScalar) g h) v.1) rfl

/-- A basis of the padded module, indexed by exactly three coordinates. -/
def referenceBasis : Module.Basis (Fin 3) F ReferencePadded :=
  (Module.finBasis F ReferencePadded).reindex (finCongr referencePadded_finrank)

/-- An unconditional three-dimensional matrix action of the full common centralizer. -/
def referenceMatrixAction : referenceCentralizer →* Matrix (Fin 3) (Fin 3) F where
  toFun g := LinearMap.toMatrix referenceBasis referenceBasis (referencePaddedAction g).toLinearMap
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.toMatrix_mul referenceBasis _ _

/-- Trivial padding does not alter the determinant of the eigenspace action. -/
theorem referenceMatrixAction_det (g : referenceCentralizer) :
    (referenceMatrixAction g).det =
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap := by
  rw [referenceMatrixAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.det_toMatrix]
  change LinearMap.det (LinearMap.prodMap
    (referenceEigenAction referenceScalar g).toLinearMap
    (LinearMap.id : Module.End F ReferencePadding)) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- Matrix coordinates preserve faithfulness of the intrinsic eigenspace action. -/
theorem referenceMatrixAction_injective_of_eigen
    (hf : Function.Injective (referenceEigenAction referenceScalar)) :
    Function.Injective referenceMatrixAction := by
  intro g h he
  apply hf
  apply LinearEquiv.ext
  intro v
  have hm : (referencePaddedAction g).toLinearMap =
      (referencePaddedAction h).toLinearMap :=
    (LinearMap.toMatrix referenceBasis referenceBasis).injective he
  exact congrArg Prod.fst (DFunLike.congr_fun hm (v, 0))

/-- A determinant-one proof places the actual matrices in the required SL₃(4). -/
def referenceCentralizerToSLOfDet
    (hd : ∀ g : referenceCentralizer,
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1) :
    referenceCentralizer →* SL(3,F) where
  toFun g := ⟨referenceMatrixAction g, (referenceMatrixAction_det g).trans (hd g)⟩
  map_one' := Subtype.ext (map_one referenceMatrixAction)
  map_mul' g h := Subtype.ext (map_mul referenceMatrixAction g h)

/-- The concrete special-linear homomorphism inherits eigenspace faithfulness. -/
theorem referenceCentralizerToSLOfDet_injective
    (hd : ∀ g : referenceCentralizer,
      LinearMap.det (referenceEigenAction referenceScalar g).toLinearMap = 1)
    (hf : Function.Injective (referenceEigenAction referenceScalar)) :
    Function.Injective (referenceCentralizerToSLOfDet hd) := by
  intro g h he
  exact referenceMatrixAction_injective_of_eigen hf (congrArg Subtype.val he)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
