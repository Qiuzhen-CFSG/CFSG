module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ToralConjugacy
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Normalization

set_option backward.isDefEq.respectTransparency false
/-!
# Actual F4 reflection lifts and converse toral conjugacy

The constructed opposite-root SL₂ chart supplies an involutory normalizer word.
Its torus formula and proved Cartan normalization identify its action with the
actual root reflection. Since reflections generate the standard Weyl group,
the full normalizer action is onto. Character evaluation then converts each
Weyl orbit equality into actual ambient conjugacy, in both raw and positive
left-character conventions.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3.9(5), and
GLS3 §1.9.5(c)--(f). The same literal reflection lifts feed connectedness of
semisimple centralizers.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup

def reflectionChart (r : typeF4Roots) :
    BinaryOppositeRootSL2Chart (F4Chevalley.splitTorus (k := F)) (F4Chevalley.rootSubgroup r)
      (F4Chevalley.rootSubgroup (typeF4RootPairing.reflectionPerm r r)) :=
  Classical.choice (F4Chevalley.ConcreteCharts.literalRootSL2Charts r)

private theorem root_equation (r : typeF4Roots) :
    RootWeightEquation (F4Chevalley.splitTorus (k := F)) (F4Chevalley.rootSubgroup r)
      (F4Chevalley.rootWeight r) := ((rootData_isRealization_charTwo (F := F)).2.2.1 ⟨r⟩).2

private theorem negative_equation (r : typeF4Roots) :
    RootWeightEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootSubgroup (typeF4RootPairing.reflectionPerm r r))
      (F4Chevalley.rootWeight r)⁻¹ := by
  have he := (rootData_isRealization_charTwo (F := F)).2.2.2.1 ⟨r⟩
  change F4Chevalley.rootWeight (k := F) (typeF4RootPairing.reflectionPerm r r) =
    (F4Chevalley.rootWeight r)⁻¹ at he
  rw [← he]
  exact root_equation _

def reflectionLift (r : typeF4Roots) : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup :=
  ⟨(reflectionChart r).weyl, (reflectionChart r).weyl_mem_normalizer
    (F4Chevalley.rootWeight r) (root_equation r) (negative_equation r)⟩

theorem reflectionLift_val (r : typeF4Roots) :
    (reflectionLift (F := F) r).val = (reflectionChart r).weyl := by
  unfold reflectionLift
  rfl

private theorem reflectionLift_torus (r : typeF4Roots)
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (torusConjugation (reflectionLift r)⁻¹).onPoints t =
      t * ((reflectionChart r).cocharacter.onPoints ((F4Chevalley.rootWeight r).onPoints t))⁻¹ := by
  apply (F4Chevalley.splitTorus (k := F)).inclusion_injective
  change (F4Chevalley.splitTorus (k := F)).includePoint _ =
    (F4Chevalley.splitTorus (k := F)).includePoint _
  rw [torusConjugation_include]
  change (reflectionChart r).weyl⁻¹ * _ * ((reflectionChart r).weyl⁻¹)⁻¹ = _
  rw [inv_inv, (reflectionChart r).weyl_inv]
  have h := (reflectionChart r).weyl_conjugation (F4Chevalley.rootWeight r)
    (root_equation r) (negative_equation r) t
  change (reflectionChart r).weyl * (F4Chevalley.splitTorus (k := F)).includePoint t *
    (reflectionChart r).weyl⁻¹ = (F4Chevalley.splitTorus (k := F)).includePoint _ at h
  simpa only [(reflectionChart r).weyl_inv] using h

omit [CharP F 2] in
private theorem eval_mul_zpow (χ ψ : TorusWeight (F4Chevalley.splitTorus (k := F)))
    (m : ℤ) (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    (χ * ψ ^ m).pointCharacter t = χ.pointCharacter t * ψ.pointCharacter t ^ m := by
  let ev : TorusWeight (F4Chevalley.splitTorus (k := F)) →* F :=
    { toFun := fun η => η.pointCharacter t
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (ev.map_mul χ (ψ ^ m)).trans
    (congrArg (fun z : F => ev χ * z) (map_zpow ev ψ m))

theorem normalizerRootAction_reflectionLift (r s : typeF4Roots) :
    normalizerRootAction (reflectionLift (F := F) r) s = typeF4RootPairing.reflectionPerm r s := by
  apply F4Chevalley.concreteRootWeight_injective (k := F)
  rw [normalizerRootAction_weight]
  have hrefl := (rootData_isRealization_charTwo (F := F)).2.2.2.2.2.1 ⟨r⟩ ⟨s⟩
  change F4Chevalley.rootWeight (k := F) (typeF4RootPairing.reflectionPerm r s) =
    F4Chevalley.rootWeight s * F4Chevalley.rootWeight r ^ (-typeF4RootPairing.pairingIn ℤ s r) at hrefl
  rw [hrefl]
  apply TorusCharacter.pointCharacter_injective
  ext t
  rw [weightAction_apply, reflectionLift_torus, map_mul, map_inv, eval_mul_zpow]
  let : Finite (rootData (F := F)).Root :=
    Finite.of_injective (rootSystemModel (F := F)).rootEquiv
      (rootSystemModel (F := F)).rootEquiv.injective
  have hcart : WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight s) (reflectionChart r).cocharacter
      (typeF4RootPairing.pairingIn ℤ s r) :=
    (rootData (F := F)).chart_isCartan rootData_isRealization_charTwo
      F4Chevalley.splitTorus_isSubtorus ⟨r⟩ (reflectionChart r) ⟨s⟩
  rw [hcart]
  change _ * ((F4Chevalley.rootWeight r).pointCharacter t ^
    typeF4RootPairing.pairingIn ℤ s r)⁻¹ = _
  rw [zpow_neg]

theorem normalizerWeyl_reflectionLift (r : typeF4Roots) :
    normalizerWeyl (reflectionLift (F := F) r) = RootPairing.weylGroup.ofIdx typeF4RootPairing r := by
  apply F4WeightAction.representation_injective
  have he := F4WeightAction.addHom_ext_roots
    (F4WeightAction.representation (normalizerWeyl (reflectionLift (F := F) r))).toAddMonoidHom
    (F4WeightAction.representation (RootPairing.weylGroup.ofIdx typeF4RootPairing r)).toAddMonoidHom
    (fun s => by
      change F4WeightAction.representation _ (F4WeightAction.rootWeight s) =
        F4WeightAction.representation _ (F4WeightAction.rootWeight s)
      rw [F4WeightAction.representation_root, F4WeightAction.representation_root,
        normalizerWeyl_spec, normalizerRootAction_reflectionLift]
      rfl)
  exact LinearEquiv.ext (fun a => DFunLike.congr_fun he a)

theorem normalizerWeyl_surjective : Function.Surjective (normalizerWeyl (F := F)) := by
  intro w
  have h : w ∈ (normalizerWeyl (F := F)).range := by
    obtain ⟨w, hw⟩ := w
    induction hw using RootPairing.weylGroup.induction with
    | mem r => exact ⟨reflectionLift r, normalizerWeyl_reflectionLift r⟩
    | one => exact (normalizerWeyl (F := F)).range.one_mem
    | mul v w hv hw ihv ihw => exact (normalizerWeyl (F := F)).range.mul_mem ihv ihw
  exact h

/-- Every equality of torus evaluations along the actual Weyl action is
realized by an ambient conjugator. -/
theorem ambient_isConj_of_weyl_evaluations
    (x y : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (w : F4WeightAction.Weyl)
    (he : ∀ a, rawEvaluation y a = rawEvaluation x (F4WeightAction.representation w a)) :
    IsConj ((F4Chevalley.splitTorus (k := F)).includePoint x)
      ((F4Chevalley.splitTorus (k := F)).includePoint y) := by
  obtain ⟨n, hn⟩ := normalizerWeyl_surjective (F := F) w
  have hp : (torusConjugation n⁻¹).onPoints x = y := by
    apply rawEvaluation_injective
    apply AddMonoidHom.ext
    intro a
    have h := rawEvaluation_normalizer n x a
    rw [hn] at h
    exact h.symm.trans (he a).symm
  apply isConj_iff.mpr
  refine ⟨n.val⁻¹, ?_⟩
  have h := congrArg (F4Chevalley.splitTorus (k := F)).includePoint hp
  rw [torusConjugation_include, Subgroup.coe_inv, inv_inv] at h
  simpa only [inv_inv] using h

/-- The same converse in the positive left-character convention of the Ree
fundamental-coordinate class map. -/
theorem ambient_isConj_of_weyl_leftCharacter
    (x y : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (w : F4WeightAction.Weyl)
    (he : ∀ a, (leftCharacter a).pointCharacter y =
      (leftCharacter (F4WeightAction.representation w a)).pointCharacter x) :
    IsConj ((F4Chevalley.splitTorus (k := F)).includePoint x)
      ((F4Chevalley.splitTorus (k := F)).includePoint y) := by
  apply ambient_isConj_of_weyl_evaluations x y w
  intro a
  rw [rawEvaluation_apply, rawEvaluation_apply]
  apply Additive.ofMul.injective
  apply Units.ext
  change (rawCharacter a).pointCharacter y =
    (rawCharacter (F4WeightAction.representation w a)).pointCharacter x
  simpa only [leftCharacter, map_neg, neg_neg] using he (-a)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
