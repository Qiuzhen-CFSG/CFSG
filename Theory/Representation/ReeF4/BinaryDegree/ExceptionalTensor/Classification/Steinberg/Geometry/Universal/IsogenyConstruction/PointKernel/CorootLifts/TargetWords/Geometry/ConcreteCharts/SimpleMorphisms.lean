module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Regularity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Restriction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.ElementaryCurves
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Multiplication

/-!
# Assembly of the polynomial simple-root SL₂ maps

The explicit matrix candidate has polynomial entries on SL₂. Its identity
and multiplication laws therefore construct a regular ambient morphism. The
two elementary-curve formulas identify its upper and lower curves with the
literal integral root curves; elementary generation puts its image in F4.

The proved matrix multiplication law and elementary-curve identities discharge
every input to the construction in characteristic two. The resulting family
`simpleRootSL2Morphisms` preserves the literal parameters on both root curves.
The conditional assembly remains available over general algebraically closed
fields with the matrix identities as explicit inputs.
Source: the integral parametrizations underlying GLS3, 1.9.5(d), Remarks
1.9.6 and the defining formulas in 1.12.1.
-/

public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local instance simpleMorphismsAssemblyNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

variable (i : typeF4RootPairing_base.support)
variable (hone : simpleSL2Matrix i (1 : Matrix (Fin 2) (Fin 2) k) = 1)
variable (hmul : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) k,
  simpleSL2Matrix i ((A * B : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
    simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *
      simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k))

/-- The positive matrix identity gives exact agreement of regular upper curves. -/
lemma simpleSL2AmbientMorphism_upper
    (hp : ∀ t : k, simpleSL2Matrix i (Matrix.transvection 0 1 t) = positiveMatrix i t) :
    (simpleSL2AmbientMorphism i hone hmul).comp standardSL2UpperMorphism =
      ambientRootMorphism i := by
  apply Morphism.ext
  funext x
  change (simpleSL2AmbientMorphism i hone hmul).onPoints
    (standardSL2UpperMorphism.onPoints x) = (ambientRootMorphism i).onPoints x
  rw [← kPlusPoint_coordinate x]
  rw [standardSL2UpperMorphism_kPlusPoint, simpleSL2AmbientMorphism_apply,
    ← matrixToAmbient_root]
  apply congrArg matrixToAmbient
  apply Units.ext
  change simpleSL2Matrix i (Matrix.transvection 0 1 _) = (rootCurve i _).val
  rw [show rootCurve (S := k) i (Multiplicative.toAdd (additiveGroupPointEquiv k x)) =
      positiveUnit i (Multiplicative.toAdd (additiveGroupPointEquiv k x)) from
    rootCurveUnit_simple i _]
  exact hp _

/-- The negative matrix identity gives exact agreement of regular lower curves. -/
lemma simpleSL2AmbientMorphism_lower
    (hm : ∀ t : k, simpleSL2Matrix i (Matrix.transvection 1 0 t) = negativeMatrix i t) :
    (simpleSL2AmbientMorphism i hone hmul).comp standardSL2LowerMorphism =
      ambientRootMorphism (-i : Root) := by
  apply Morphism.ext
  funext x
  change (simpleSL2AmbientMorphism i hone hmul).onPoints
    (standardSL2LowerMorphism.onPoints x) = (ambientRootMorphism (-i : Root)).onPoints x
  rw [← kPlusPoint_coordinate x]
  rw [standardSL2LowerMorphism_kPlusPoint, simpleSL2AmbientMorphism_apply,
    ← matrixToAmbient_root]
  apply congrArg matrixToAmbient
  apply Units.ext
  change simpleSL2Matrix i (Matrix.transvection 1 0 _) = (rootCurve (-i : Root) _).val
  rw [show rootCurve (S := k) (-i : Root) (Multiplicative.toAdd (additiveGroupPointEquiv k x)) =
      negativeUnit i (Multiplicative.toAdd (additiveGroupPointEquiv k x)) from
    rootCurveUnit_neg_simple i _]
  exact hm _

/-- Conditional assembly from explicit polynomial identities, retaining literal parameters. -/
theorem simpleRootSL2Morphisms_of_matrix_laws
    (hMul : ∀ (i : typeF4RootPairing_base.support)
      (A B : Matrix.SpecialLinearGroup (Fin 2) k),
      simpleSL2Matrix i ((A * B : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
        simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *
          simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k))
    (hUpper : ∀ (i : typeF4RootPairing_base.support) (t : k),
      simpleSL2Matrix i (Matrix.transvection 0 1 t) = positiveMatrix i t)
    (hLower : ∀ (i : typeF4RootPairing_base.support) (t : k),
      simpleSL2Matrix i (Matrix.transvection 1 0 t) = negativeMatrix i t) :
    ∀ i : typeF4RootPairing_base.support,
      ∃ f : Morphism (slVariety k 2) (F4Chevalley.Carrier (k := k)),
        f.comp standardSL2UpperMorphism = rootMorphism i ∧
        f.comp standardSL2LowerMorphism = rootMorphism (typeF4RootPairing.reflectionPerm i i) := by
  intro i
  let f := simpleSL2AmbientMorphism i (simpleSL2Matrix_one i) (hMul i)
  have hp : f.comp standardSL2UpperMorphism = ambientRootMorphism i :=
    simpleSL2AmbientMorphism_upper i (simpleSL2Matrix_one i) (hMul i) (hUpper i)
  have hm : f.comp standardSL2LowerMorphism = ambientRootMorphism (-i : Root) :=
    simpleSL2AmbientMorphism_lower i (simpleSL2Matrix_one i) (hMul i) (hLower i)
  exact ⟨restrictAmbientSL2 i f hp hm,
    restrictAmbientSL2_upper i f hp hm, restrictAmbientSL2_lower i f hp hm⟩

/-- Every literal simple F4 root pair is the image of the standard upper and lower
SL₂ curves under a regular algebraic-group morphism, with unchanged parameters. -/
theorem simpleRootSL2Morphisms [CharP k 2] :
    ∀ i : typeF4RootPairing_base.support,
      ∃ f : Morphism (slVariety k 2) (F4Chevalley.Carrier (k := k)),
        f.comp standardSL2UpperMorphism = rootMorphism i ∧
        f.comp standardSL2LowerMorphism =
          rootMorphism (typeF4RootPairing.reflectionPerm i i) :=
  simpleRootSL2Morphisms_of_matrix_laws simpleSL2Matrix_mul
    simpleSL2Matrix_upper simpleSL2Matrix_lower

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
