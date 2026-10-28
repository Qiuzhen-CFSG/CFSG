module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleWords

/-!
# Restricting a compatible ambient SL₂ map to F4

The two literal simple-root curves lie in the closed Chevalley carrier.
Since the upper and lower curves generate SL₂, any ambient morphism agreeing
with those curves has image in the carrier. Codomain restriction is regular
and preserves the literal parameters in both directions.

The ambient morphism is an explicit input here. This is the restriction step
in the integral rank-one construction underlying GLS3, 1.9.5(d) and 1.12.1.
-/

public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local instance simpleMorphismsRestrictionNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg

/-- Agreement on the two elementary curves puts an ambient SL₂ map in the F4 carrier. -/
lemma ambientSL2_mem_carrier (i : typeF4RootPairing_base.support)
    (f : Morphism (slVariety k 2) (Ambient k))
    (hp : f.comp standardSL2UpperMorphism = ambientRootMorphism i)
    (hm : f.comp standardSL2LowerMorphism = ambientRootMorphism (-i : Root))
    (x : Variety.Point (slVariety k 2)) :
    f.onPoints x ∈ (ambientClosedCarrier (k := k)).toSubgroup := by
  have hle : Subgroup.closure
      (Set.range (standardSL2UpperMorphism (k := k)).onPoints ∪
        Set.range (standardSL2LowerMorphism (k := k)).onPoints) ≤
      (ambientCarrierSubgroup (k := k)).comap f.onPoints := by
    apply (Subgroup.closure_le _).mpr
    rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · change (f.comp standardSL2UpperMorphism).onPoints z ∈ ambientCarrierSubgroup (k := k)
      rw [hp]
      exact ambientRoot_mem_carrier i z
    · change (f.comp standardSL2LowerMorphism).onPoints z ∈ ambientCarrierSubgroup (k := k)
      rw [hm]
      exact ambientRoot_mem_carrier (-i : Root) z
  rw [standardSL2_upper_lower_generate] at hle
  exact hle (Subgroup.mem_top x)

/-- Restriction of a compatible ambient map to the literal closed F4 carrier. -/
def restrictAmbientSL2 (i : typeF4RootPairing_base.support)
    (f : Morphism (slVariety k 2) (Ambient k))
    (hp : f.comp standardSL2UpperMorphism = ambientRootMorphism i)
    (hm : f.comp standardSL2LowerMorphism = ambientRootMorphism (-i : Root)) :
    Morphism (slVariety k 2) (Carrier (k := k)) :=
  f.codRestrictClosedSubgroup (ambientClosedCarrier (k := k))
    (ambientSL2_mem_carrier i f hp hm)

lemma restrictAmbientSL2_upper (i : typeF4RootPairing_base.support)
    (f : Morphism (slVariety k 2) (Ambient k))
    (hp : f.comp standardSL2UpperMorphism = ambientRootMorphism i)
    (hm : f.comp standardSL2LowerMorphism = ambientRootMorphism (-i : Root)) :
    (restrictAmbientSL2 i f hp hm).comp standardSL2UpperMorphism = rootMorphism i := by
  apply Morphism.ext
  funext x
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  change (ambientClosedCarrier (k := k)).inclusion.onPoints
    ((restrictAmbientSL2 i f hp hm).onPoints (standardSL2UpperMorphism.onPoints x)) =
      (ambientClosedCarrier (k := k)).inclusion.onPoints ((rootMorphism i).onPoints x)
  rw [restrictAmbientSL2, Morphism.codRestrictClosedSubgroup_inclusion_apply,
    rootMorphism_inclusion_apply]
  exact congrArg (fun g : Morphism (KPlus k) (Ambient k) => g.onPoints x) hp

lemma restrictAmbientSL2_lower (i : typeF4RootPairing_base.support)
    (f : Morphism (slVariety k 2) (Ambient k))
    (hp : f.comp standardSL2UpperMorphism = ambientRootMorphism i)
    (hm : f.comp standardSL2LowerMorphism = ambientRootMorphism (-i : Root)) :
    (restrictAmbientSL2 i f hp hm).comp standardSL2LowerMorphism =
      rootMorphism (typeF4RootPairing.reflectionPerm i i) := by
  apply Morphism.ext
  funext x
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  change (ambientClosedCarrier (k := k)).inclusion.onPoints
    ((restrictAmbientSL2 i f hp hm).onPoints (standardSL2LowerMorphism.onPoints x)) =
      (ambientClosedCarrier (k := k)).inclusion.onPoints ((rootMorphism (-i : Root)).onPoints x)
  rw [restrictAmbientSL2, Morphism.codRestrictClosedSubgroup_inclusion_apply,
    rootMorphism_inclusion_apply]
  exact congrArg (fun g : Morphism (KPlus k) (Ambient k) => g.onPoints x) hm

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
