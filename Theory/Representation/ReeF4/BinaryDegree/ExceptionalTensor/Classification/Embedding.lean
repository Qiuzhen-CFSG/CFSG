module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Coefficient embeddings into the closed algebraic F4 carrier

Entrywise coefficient base change on the integral root matrices is transported
through the matrix/general-linear-point equivalence. Subgroup closure induction
puts its image in the actual closed F4 carrier. Injectivity follows entrywise,
and the root-generator formula identifies the image with the algebraic root
morphisms used by the highest-weight predicates.

This constructs the concrete embedding required for GLS3, §2.8. It does not
identify the entire algebraic exceptional fixed group or assert Steinberg's
representation classification. The two carriers use the same integral root
curves from GLS3, §2.2 and Steinberg's Chevalley construction.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
noncomputable section

/-- The ambient matrix group and the points of the ambient general linear variety. -/
def ambientUnitsEquiv :
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ ≃*
      Variety.Point (F4Chevalley.Ambient F) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((Matrix.GeneralLinearGroup.toLin'
      (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))).symm.trans
      (translationGLPointMulEquiv _).symm)

theorem ambientUnitsEquiv_rootCurve (r : F4Chevalley.Root) (t : F) :
    ambientUnitsEquiv (F4Chevalley.rootCurve r t) =
      (F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint t) := by
  rw [F4Chevalley.ambientRootMorphism_apply]
  rfl

/-- Coefficient base change into the ambient algebraic group. -/
def ambientMap {k : ℕ} (f : CoefficientField k →+* F) :
    MatrixUnits k →* Variety.Point (F4Chevalley.Ambient F) :=
  ambientUnitsEquiv.toMonoidHom.comp (Units.map f.mapMatrix.toMonoidHom)

omit [IsAlgClosed F] in
theorem unitsMap_rootCurve {k : ℕ} (f : CoefficientField k →+* F)
    (r : F4Chevalley.Root) (t : CoefficientField k) :
    Units.map f.mapMatrix.toMonoidHom (F4Chevalley.rootCurve r t) =
      F4Chevalley.rootCurve r (f t) := by
  apply Units.ext
  change (↑(F4Chevalley.rootCurve r t) : MatrixCarrier k).map f = _
  rw [F4Chevalley.rootCurve_matrix_formula, F4Chevalley.rootCurve_matrix_formula]
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    specializeMatrix, Matrix.one_apply, apply_ite f]

@[simp] theorem ambientMap_rootCurve {k : ℕ} (f : CoefficientField k →+* F)
    (r : F4Chevalley.Root) (t : CoefficientField k) :
    ambientMap f (F4Chevalley.rootCurve r t) =
      (F4Chevalley.ambientRootMorphism r).onPoints (kPlusPoint (f t)) := by
  change ambientUnitsEquiv (Units.map f.mapMatrix.toMonoidHom _) = _
  rw [unitsMap_rootCurve, ambientUnitsEquiv_rootCurve]

theorem ambientMap_mem {k : ℕ} (f : CoefficientField k →+* F)
    {x : MatrixUnits k} (hx : x ∈ SplitGroup k) :
    ambientMap f x ∈ F4Chevalley.ambientCarrierSubgroup (k := F) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨⟨r, t⟩, rfl⟩
      simpa only [rootGenerator_apply, ambientMap_rootCurve] using
        F4Chevalley.ambientRoot_mem_carrier r (kPlusPoint (f t))
  | one => simp
  | mul x y _ _ hx hy =>
      simpa only [map_mul] using (F4Chevalley.ambientCarrierSubgroup (k := F)).mul_mem hx hy
  | inv x _ hx =>
      simpa only [map_inv] using (F4Chevalley.ambientCarrierSubgroup (k := F)).inv_mem hx

/-- The actual coefficient embedding into the closed algebraic F4 carrier. -/
def splitEmbedding {k : ℕ} (f : CoefficientField k →+* F) :
    SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)) where
  toFun x := (F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv.symm
    ⟨ambientMap f x.val, ambientMap_mem f x.property⟩
  map_one' := by
    apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
    change ambientMap f 1 = 1
    exact map_one _
  map_mul' x y := by
    apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
    change ambientMap f (x.val * y.val) = ambientMap f x.val * ambientMap f y.val
    exact map_mul _ _ _

@[simp] theorem inclusion_splitEmbedding {k : ℕ} (f : CoefficientField k →+* F)
    (x : SplitGroup k) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints (splitEmbedding f x) =
      ambientMap f x.val := by rfl

theorem splitEmbedding_injective {k : ℕ} (f : CoefficientField k →+* F) :
    Function.Injective (splitEmbedding f) := by
  intro x y h
  have h' := congrArg (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints h
  simp only [inclusion_splitEmbedding] at h'
  have hm := ambientUnitsEquiv.injective h'
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun z : (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ =>
    z.val i j) hm

@[simp] theorem splitEmbedding_rootGenerator {k : ℕ} (f : CoefficientField k →+* F)
    (r : F4Chevalley.Root) (t : CoefficientField k) :
    splitEmbedding f (rootGeneratorInGroup k r t) = algebraicRootElement r (f t) := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  rw [inclusion_splitEmbedding]
  change ambientMap f (F4Chevalley.rootCurve r t) =
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      ((F4Chevalley.rootMorphism r).onPoints (kPlusPoint (f t)))
  rw [ambientMap_rootCurve, F4Chevalley.rootMorphism_inclusion_apply]

/-- An algebraically closed characteristic-two field contains the finite Ree field. -/
def coefficientHom (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2] (k : ℕ) :
    CoefficientField k →+* F := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  exact (IsAlgClosed.lift (R := ZMod 2) (S := CoefficientField k) (M := F)).toRingHom

/-- The base-change embedding is uniquely determined by its actual root elements. -/
theorem splitEmbedding_unique {k : ℕ} (f : CoefficientField k →+* F)
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (hι : ∀ r t, ι (rootGeneratorInGroup k r t) = algebraicRootElement r (f t)) :
    ι = splitEmbedding f := by
  apply splitGroup_hom_ext
  intro r t
  rw [hι, splitEmbedding_rootGenerator]

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification
