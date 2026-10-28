module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison.Coordinates
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.HighestUnipotent.OrthogonalModel

/-!
# The natural orthogonal action and its scalar quotient

Conjugation on endomorphisms kills the literal scalar subgroup of the
Siegel-generated Omega carrier. The resulting projective action makes sense
in odd characteristic without assuming a model comparison. `NaturalPinning`
specifies the remaining eight-dimensional geometry: the four simple-root
SL₂ maps, their actual matrix formulas, and the four determinant-space ranges.
Its fields involve only the orthogonal carrier, not the Geck group.

Sources: GLS3 §§2.4, 2.6–2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
open ClassicalOrthogonal
variable (F : Type*) [Field F]

/-- The actual natural matrix of an elementary isometry, in `formD 4` coordinates. -/
def naturalMatrix : OmegaPlus 4 F →* NaturalMatrix F where
  toFun x := LinearMap.toMatrix' x.val.val.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' _ _ := LinearMap.toMatrix'_mul _ _

@[simp] theorem naturalMatrix_mulVec (x : OmegaPlus 4 F) (v : VectorD 4 F) :
    naturalMatrix F x *ᵥ v = x.val.val v := LinearMap.toMatrix'_mulVec _ _

/-- Conjugation on all endomorphisms of the literal eight-space. -/
def conjugation : OmegaPlus 4 F →* Module.End F (NaturalMatrix F) where
  toFun x := LinearMap.mulLeftRight F (naturalMatrix F x, naturalMatrix F x⁻¹)
  map_one' := by
    ext M
    simp [LinearMap.mulLeftRight]
  map_mul' x y := by
    ext M
    simp [LinearMap.mulLeftRight, mul_assoc]

@[simp] theorem conjugation_apply (x : OmegaPlus 4 F) (M : NaturalMatrix F) :
    conjugation F x M = naturalMatrix F x * M * naturalMatrix F x⁻¹ := rfl

private theorem naturalMatrix_scalar (x : OmegaPlus 4 F) (c : F)
    (h : ∀ v, x.val.val v = c • v) : naturalMatrix F x = c • 1 := by
  apply Matrix.mulVec_injective
  funext v
  rw [naturalMatrix_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact h v

/-- Actual elementary scalar isometries act trivially by conjugation. -/
theorem scalar_conjugation (x : OmegaPlus 4 F)
    (hx : x ∈ elementaryScalarSubgroup (formD 4 F)) : conjugation F x = 1 := by
  obtain ⟨c, hc, hcx⟩ := hx
  have hci : ∀ v, (x⁻¹).val.val v = c • v := by
    intro v
    apply x.val.val.injective
    change x.val.val (x.val.val.symm v) = x.val.val (c • v)
    rw [LinearEquiv.apply_symm_apply, map_smul, hcx, smul_smul, ← pow_two, hc, one_smul]
  apply LinearMap.ext
  intro M
  change naturalMatrix F x * M * naturalMatrix F x⁻¹ = M
  rw [naturalMatrix_scalar F x c hcx, naturalMatrix_scalar F x⁻¹ c hci]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    smul_smul, ← pow_two, hc, one_smul]

/-- The action descends through exactly the scalar quotient in the target. -/
def projectiveAdjoint : POmegaPlus 4 F →* Module.End F (NaturalMatrix F) :=
  QuotientGroup.lift (elementaryScalarSubgroup (formD 4 F)) (conjugation F)
    (scalar_conjugation F)

@[simp] theorem projectiveAdjoint_mk (x : OmegaPlus 4 F) :
    projectiveAdjoint F (projectiveElementaryMap (formD 4 F) x) = conjugation F x := rfl

/-- The remaining kernel assertion tests only the signed Geck coordinate image. -/
def ScalarDetection : Prop := ∀ x : OmegaPlus 4 F,
  (∀ v, conjugation F x (embedding F v) = embedding F v) →
    projectiveElementaryMap (formD 4 F) x = 1

/-- The same detection statement directly on the project's projective carrier. -/
theorem projective_detect (h : ScalarDetection F) (x : POmegaPlus 4 F)
    (hx : ∀ v, projectiveAdjoint F x (embedding F v) = embedding F v) : x = 1 := by
  obtain ⟨x, rfl⟩ := projectiveElementaryMap_surjective (formD 4 F) x
  exact h x hx

/-- The same central-times-arms Weyl word as the Geck highest-root definition. -/
def naturalHighestWeyl (H : Fin 4 → SL(2, F) →* OmegaPlus 4 F) : OmegaPlus 4 F :=
  H 1 (weylMatrix F) *
    (H 0 (weylMatrix F) * H 2 (weylMatrix F) *
      H 3 (weylMatrix F))

def naturalHighestHom (H : Fin 4 → SL(2, F) →* OmegaPlus 4 F) :
    SL(2, F) →* POmegaPlus 4 F :=
  (projectiveElementaryMap (formD 4 F)).comp
    ((MulAut.conj (naturalHighestWeyl F H)).toMonoidHom.comp (H 1))

/-- A contract entirely in the literal natural orthogonal eight-space. -/
structure NaturalPinning where
  hom : Fin 4 → SL(2, F) →* OmegaPlus 4 F
  positive : ∀ i t, naturalMatrix F (hom i
    (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) =
      naturalCurve F i true t
  negative : ∀ i t, naturalMatrix F (hom i
    (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) =
      naturalCurve F i false t
  highest_range : (naturalHighestHom F hom).range = OrthogonalModel.highest.range
  armZero_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 0)).range =
    OrthogonalModel.armZero.range
  armTwo_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 2)).range =
    OrthogonalModel.armTwo.range
  armThree_range : ((projectiveElementaryMap (formD 4 F)).comp (hom 3)).range =
    OrthogonalModel.armThree.range

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent.OrthogonalComparison
