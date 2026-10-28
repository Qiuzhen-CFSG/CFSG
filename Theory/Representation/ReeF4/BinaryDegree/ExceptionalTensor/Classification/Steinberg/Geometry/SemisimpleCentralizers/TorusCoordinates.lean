module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Automorphisms
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Realization
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence.Action
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# The actual F4 torus-normalizer action

The literal split-torus character lattice is the full integral weight lattice.
Conjugation permutes actual root subgroups and their characters, hence preserves
root negation and addition. The F4 automorphism calculation places this action
in the standard Weyl group. Root characters span the lattice, so the root formula
extends to every character and point evaluation, retaining the inverse-pullback
convention and both raw and positive left characters.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3. This is the
literal torus interface for semisimple centralizers and the Ree class count.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance torusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

private def characterTransport : TorusCharacter (dVariety F 4) ≃*
    TorusWeight (F4Chevalley.splitTorus (k := F)) where
  toFun := TorusCharacter.pullback (F4Chevalley.splitTorusIso (k := F)).inv
  invFun := TorusCharacter.pullback (F4Chevalley.splitTorusIso (k := F)).hom
  left_inv χ := by
    apply Morphism.ext
    funext t
    change χ.onPoints ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
      ((F4Chevalley.splitTorusIso (k := F)).hom.onPoints t)) = χ.onPoints t
    rw [(F4Chevalley.splitTorusIso (k := F)).hom_inv_id]
  right_inv χ := by
    apply Morphism.ext
    funext t
    change χ.onPoints ((F4Chevalley.splitTorusIso (k := F)).hom.onPoints
      ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints t)) = χ.onPoints t
    rw [(F4Chevalley.splitTorusIso (k := F)).inv_hom_id]
  map_mul' := (TorusCharacter.pullback (F4Chevalley.splitTorusIso (k := F)).inv).map_mul

def characterEquiv : F4WeightAction.Weight ≃+ Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) :=
  (dLaurentCharacterAddEquiv 4).trans characterTransport.toAdditive

theorem characterEquiv_apply (a : F4WeightAction.Weight) :
    characterEquiv (F := F) a = Additive.ofMul (rawCharacter a) := by
  unfold characterEquiv characterTransport
  rfl

theorem characterEquiv_root (r : typeF4Roots) :
    characterEquiv (F := F) (F4WeightAction.rootWeight r) =
      Additive.ofMul (F4Chevalley.rootWeight r) := by
  rw [characterEquiv_apply]
  change rawCharacter (F := F) (F4WeightAction.rootWeight r) = F4Chevalley.rootWeight r
  apply TorusCharacter.pointCharacter_injective
  ext s
  exact (congrArg Units.val (F4Chevalley.splitTorusCharacter_apply_point
    (F4Chevalley.torusRootExponent r) s)).trans (F4Chevalley.rootWeight_pointCharacter r s).symm

variable [CharP F 2]

def normalizerRootAction :
    (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup →* Equiv.Perm typeF4Roots where
  toFun n := Equiv.permCongr Equiv.ulift (rootAction rootData_isRealization_charTwo n)
  map_one' := by rw [map_one]; rfl
  map_mul' n m := by rw [map_mul]; rfl

theorem normalizerRootAction_apply (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (r : typeF4Roots) :
    normalizerRootAction n r = (rootAction rootData_isRealization_charTwo n ⟨r⟩).down := by
  unfold normalizerRootAction
  rfl

theorem normalizerRootAction_weight (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (r : typeF4Roots) :
    F4Chevalley.rootWeight (normalizerRootAction n r) = weightAction n (F4Chevalley.rootWeight r) :=
  rootAction_weight rootData_isRealization_charTwo n ⟨r⟩

theorem normalizerRootAction_neg (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (r : typeF4Roots) :
    normalizerRootAction n (typeF4RootPairing.reflectionPerm r r) =
      typeF4RootPairing.reflectionPerm (normalizerRootAction n r) (normalizerRootAction n r) :=
  congrArg ULift.down (rootAction_neg rootData_isRealization_charTwo n ⟨r⟩)

omit [CharP F 2] in
private theorem root_character_add_iff (r s q : typeF4Roots) :
    typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s ↔
      F4Chevalley.rootWeight (k := F) q = F4Chevalley.rootWeight r * F4Chevalley.rootWeight s := by
  rw [← F4WeightAction.realization_root q, ← F4WeightAction.realization_root r,
    ← F4WeightAction.realization_root s, ← map_add, F4WeightAction.realization_injective.eq_iff]
  rw [← (characterEquiv (F := F)).injective.eq_iff, map_add,
    characterEquiv_root, characterEquiv_root, characterEquiv_root]
  rfl

theorem normalizerRootAction_add (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (r s q : typeF4Roots) :
    typeF4RootPairing.root q = typeF4RootPairing.root r + typeF4RootPairing.root s ↔
      typeF4RootPairing.root (normalizerRootAction n q) =
        typeF4RootPairing.root (normalizerRootAction n r) +
          typeF4RootPairing.root (normalizerRootAction n s) := by
  have hf : Function.Injective (weightAction n) := by
    intro a b h
    apply TorusCharacter.pointCharacter_injective
    ext t
    have ht := congrArg (fun χ : TorusWeight (F4Chevalley.splitTorus (k := F)) =>
      χ.pointCharacter ((torusConjugation n).onPoints t)) h
    simp only [weightAction_apply] at ht
    have hid : (torusConjugation n⁻¹).onPoints ((torusConjugation n).onPoints t) = t := by
      apply (F4Chevalley.splitTorus (k := F)).inclusion_injective
      change (F4Chevalley.splitTorus (k := F)).includePoint _ =
        (F4Chevalley.splitTorus (k := F)).includePoint t
      rw [torusConjugation_include, torusConjugation_include]
      rw [Subgroup.coe_inv, inv_inv]
      group
    rwa [hid] at ht
  rw [root_character_add_iff (F := F), root_character_add_iff (F := F),
    normalizerRootAction_weight, normalizerRootAction_weight, normalizerRootAction_weight,
    ← map_mul, hf.eq_iff]

theorem exists_normalizer_weyl (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup) :
    ∃ w : F4WeightAction.Weyl, typeF4RootPairing.weylGroupToPerm w = normalizerRootAction n := by
  let : Fintype typeF4Roots := Fintype.ofFinite _
  obtain ⟨f, hf⟩ := PreservesRootPairingStructure.exists_equiv typeF4RootPairing
    typeF4RootPairing typeF4RootPairing_base (normalizerRootAction n)
    ⟨normalizerRootAction_neg n, normalizerRootAction_add n⟩
  exact ⟨⟨f, F4WeightAction.aut_mem_weylGroup f⟩, hf⟩


private theorem weylPerm_injective : Function.Injective typeF4RootPairing.weylGroupToPerm := by
  intro v w h
  apply F4WeightAction.representation_injective
  apply LinearEquiv.ext
  have he := F4WeightAction.addHom_ext_roots (F4WeightAction.representation v).toAddMonoidHom
    (F4WeightAction.representation w).toAddMonoidHom (fun r => by
      change F4WeightAction.representation v (F4WeightAction.rootWeight r) =
        F4WeightAction.representation w (F4WeightAction.rootWeight r)
      rw [F4WeightAction.representation_root, F4WeightAction.representation_root, h])
  intro a
  exact DFunLike.congr_fun he a

private def chosenWeyl (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup) :
    F4WeightAction.Weyl := Classical.choose (exists_normalizer_weyl n)

private theorem chosenWeyl_spec (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup) :
    typeF4RootPairing.weylGroupToPerm (chosenWeyl n) = normalizerRootAction n :=
  Classical.choose_spec (exists_normalizer_weyl n)

/-- The actual torus normalizer acts through the standard F4 Weyl group. -/
def normalizerWeyl : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup →*
    F4WeightAction.Weyl where
  toFun := chosenWeyl
  map_one' := by apply weylPerm_injective; rw [chosenWeyl_spec, map_one, map_one]
  map_mul' n m := by
    apply weylPerm_injective
    rw [map_mul, chosenWeyl_spec, chosenWeyl_spec, chosenWeyl_spec, map_mul]

theorem normalizerWeyl_spec (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup) :
    typeF4RootPairing.weylGroupToPerm (normalizerWeyl n) = normalizerRootAction n :=
  chosenWeyl_spec n

/-- Inverse-conjugation pullback is the integral Weyl action on every actual
raw torus character, with the original F4 root labels. -/
theorem rawCharacter_normalizer (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (a : F4WeightAction.Weight) :
    rawCharacter (F4WeightAction.representation (normalizerWeyl n) a) =
      weightAction n (rawCharacter a) := by
  let f : F4WeightAction.Weight →+ Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) :=
    (characterEquiv (F := F)).toAddMonoidHom.comp
      (F4WeightAction.representation (normalizerWeyl n)).toAddMonoidHom
  let g : F4WeightAction.Weight →+ Additive (TorusWeight (F4Chevalley.splitTorus (k := F))) :=
    (weightAction n).toAdditive.comp (characterEquiv (F := F)).toAddMonoidHom
  have hfg : f = g := by
    apply F4WeightAction.addHom_ext_roots
    intro r
    change characterEquiv (F4WeightAction.representation (normalizerWeyl n) (F4WeightAction.rootWeight r)) =
      (weightAction n).toAdditive (characterEquiv (F4WeightAction.rootWeight r))
    rw [F4WeightAction.representation_root, normalizerWeyl_spec,
      characterEquiv_root, characterEquiv_root]
    exact congrArg Additive.ofMul (normalizerRootAction_weight n r)
  have he := DFunLike.congr_fun hfg a
  change characterEquiv (F4WeightAction.representation (normalizerWeyl n) a) =
    (weightAction n).toAdditive (characterEquiv a) at he
  rw [characterEquiv_apply, characterEquiv_apply] at he
  exact he

/-- The positive left-character convention has the same Weyl action. -/
theorem leftCharacter_normalizer (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (a : F4WeightAction.Weight) :
    leftCharacter (F4WeightAction.representation (normalizerWeyl n) a) =
      weightAction n (leftCharacter a) := by
  change rawCharacter (-F4WeightAction.representation (normalizerWeyl n) a) =
    weightAction n (rawCharacter (-a))
  rw [← map_neg]
  exact rawCharacter_normalizer n (-a)

/-- Evaluation on literal torus points, in the character group's unit codomain. -/
def rawEvaluation (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
    F4WeightAction.Weight →+ Additive Fˣ :=
  (torusPointEval _ t).toAdditive.comp (characterEquiv (F := F)).toAddMonoidHom

omit [CharP F 2] in
theorem rawEvaluation_apply
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (a : F4WeightAction.Weight) :
    rawEvaluation t a = Additive.ofMul (torusPointEval _ t (rawCharacter a)) := by
  change (torusPointEval _ t).toAdditive (characterEquiv a) = _
  rw [characterEquiv_apply]
  rfl

/-- This is the inverse pullback convention: the normalizer's direct conjugation
on points is contravariant on character arguments. -/
theorem rawEvaluation_normalizer (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (a : F4WeightAction.Weight) :
    rawEvaluation t (F4WeightAction.representation (normalizerWeyl n) a) =
      rawEvaluation ((torusConjugation n⁻¹).onPoints t) a := by
  rw [rawEvaluation_apply, rawEvaluation_apply, rawCharacter_normalizer]
  rfl


omit [CharP F 2] in
/-- All characters of the literal split torus are retained by these coordinates. -/
theorem rawEvaluation_injective : Function.Injective (rawEvaluation (F := F)) := by
  intro s t h
  apply (torusPointEval_bijective (F4Chevalley.splitTorus_isSubtorus (k := F))).injective
  apply MonoidHom.ext
  intro χ
  obtain ⟨a, ha⟩ := (characterEquiv (F := F)).surjective (Additive.ofMul χ)
  have he := DFunLike.congr_fun h a
  change (torusPointEval _ s).toAdditive (characterEquiv a) =
    (torusPointEval _ t).toAdditive (characterEquiv a) at he
  rw [ha] at he
  exact he

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
