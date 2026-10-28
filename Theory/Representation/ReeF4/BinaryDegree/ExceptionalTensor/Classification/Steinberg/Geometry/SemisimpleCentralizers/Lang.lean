module

public import Theory.AlgebraicGroup.Automorphisms.Lang.SquareDifferential
public import Theory.AlgebraicGroup.Automorphisms.SteinbergRootFactorsDifferential
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SourceFixedPoints
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage

/-!
# Lang correction on the actual Ree point centralizers

The exceptional algebraic F4 map is bijective on points and its square is
coordinate Frobenius. Coordinate differentiation shows that its square has
zero differential; every positive odd power has the same property. Its regular
restriction to the literal centralizer of a fixed point remains bijective, and
the actual closed inclusion transfers the square-zero differential. The proved
square-differential Lang theorem therefore corrects each ambient conjugator
whenever this centralizer is connected.

The finite-model consumer uses the original coefficient embedding and its
proved equivalence with the whole fixed group. Centralizer connectedness is
explicit and remains the independent semisimple F4 root-geometry obligation;
this file does not assert the unconditional Ree fusion theorem.

Sources: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §§8.5, 10.7–10.8
and 12.5, `refs/KGroup/GLS3/Chapter2St2.tex`; the exceptional map is the literal
source map of *Lectures on Chevalley Groups*, Theorem 28.
-/

set_option backward.isDefEq.respectTransparency false
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

/-- Regular positive powers of the concrete exceptional map. -/
@[expose] public noncomputable def powerMorphism (n : ℕ) :
    Morphism (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)) where
  toVariety := ExceptionalMorphism.morphism.toVariety.iterate n
  map_one := by
    rw [Variety.Morphism.iterate_toFun]
    exact iterate_map_one ExceptionalMorphism.morphism.onPoints n
  map_mul := by
    intro x y
    rw [Variety.Morphism.iterate_toFun]
    exact iterate_map_mul ExceptionalMorphism.morphism.onPoints n x y

public theorem powerMorphism_onPoints (n : ℕ) :
    let ψ : Monoid.End (PointGroup F) := ExceptionalMorphism.morphism.onPoints
    (powerMorphism (F := F) n).onPoints = ψ ^ n := by
  ext x
  change (ExceptionalMorphism.morphism.toVariety.iterate n).toFun x = _
  rw [Variety.Morphism.iterate_toFun]
  rfl

public theorem powerMorphism_differential (n : ℕ) :
    Bor1.identityTangentMorphismLinearMap (powerMorphism (F := F) n) =
      (Bor1.identityTangentMorphismLinearMap ExceptionalMorphism.morphism) ^ n := by
  induction n with
  | zero =>
    have heq : powerMorphism (F := F) 0 = Morphism.id _ := by
      apply Morphism.ext
      funext x
      change (ExceptionalMorphism.morphism.toVariety.iterate 0).toFun x = x
      rw [Variety.Morphism.iterate_toFun]
      rfl
    rw [heq, Bor1.identityTangentMorphismLinearMap_id, pow_zero]
    exact Module.End.one_eq_id.symm
  | succ n ih =>
    have heq : powerMorphism (F := F) (n + 1) =
        (powerMorphism n).comp ExceptionalMorphism.morphism := by
      apply Morphism.ext
      funext x
      change (ExceptionalMorphism.morphism.toVariety.iterate (n + 1)).toFun x =
        (ExceptionalMorphism.morphism.toVariety.iterate n).toFun (ExceptionalMorphism.morphism.onPoints x)
      simp only [Variety.Morphism.iterate_toFun, Function.iterate_succ_apply]
      rfl
    rw [heq, Bor1.identityTangentMorphismLinearMap_comp, ih, pow_succ]
    apply LinearMap.ext
    intro D
    rfl

/-- The odd exceptional power as an actual regular endomorphism. -/
@[expose] public noncomputable def reeMorphism (m : ℕ) :
    Morphism (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)) :=
  powerMorphism (2 * m + 1)

public theorem reeMorphism_onPoints (m : ℕ) :
    let ψ : Monoid.End (PointGroup F) := ExceptionalMorphism.morphism.onPoints
    (reeMorphism (F := F) m).onPoints = ψ ^ (2 * m + 1) :=
  powerMorphism_onPoints _

/-- The ambient map is bijective on points; a regular inverse is not asserted. -/
public theorem reeMorphism_bijective (m : ℕ) : Function.Bijective (reeMorphism (F := F) m).onPoints := by
  rw [reeMorphism_onPoints]
  exact ExceptionalMorphism.morphism_bijective.iterate (2 * m + 1)

/-- The actual ambient closed point centralizer. -/
@[expose] public noncomputable def pointCentralizer (x : PointGroup F) :
    ClosedSubgroup (F4Chevalley.Carrier (k := F)) := semisimpleCommutatorPointCentralizer x

public noncomputable instance pointCentralizerGroup (x : PointGroup F) :
    AlgebraicGroup (pointCentralizer x).carrierVariety :=
  (pointCentralizer x).carrierAlgebraicGroup

/-- The regular fixed-group endomorphism fixes every literal fixed point. -/
public theorem reeMorphism_fixed (m : ℕ) (x : SourceFixedPoints.fixedGroup (F := F) m) :
    (reeMorphism m).onPoints (x : PointGroup F) = x := by
  rw [reeMorphism_onPoints]
  exact x.property

/-- Coordinate Frobenius has zero differential on the presented F4 carrier. -/
public theorem frobenius_differential_eq_zero :
    Bor1.identityTangentMorphismLinearMap (frobeniusMorphism (F := F)) = 0 := by
  apply LinearMap.ext
  intro D
  apply Bor1.coordinateTangentMap_injective (F4Chevalley.Carrier (k := F))
  funext i
  let a := Variety.PolynomialFunction.ofPolynomial (F4Chevalley.Carrier (k := F)) (MvPolynomial.X i)
  have ha : frobeniusMorphism.toVariety.pullbackAlgHom a = a * a := by
    apply Variety.PolynomialFunction.ext
    intro x
    change evalPolynomial (frobeniusEnd x).val (MvPolynomial.X i) =
      evalPolynomial x.val (MvPolynomial.X i) * evalPolynomial x.val (MvPolynomial.X i)
    simp only [evalPolynomial_X, frobeniusEnd_coordinate, pow_two]
  change D (frobeniusMorphism.toVariety.pullbackAlgHom a) = 0
  rw [ha, Derivation.leibniz]
  exact CharTwo.add_self_eq_zero _

/-- Every odd exceptional power has square-zero differential, including m=0. -/
public theorem reeMorphism_square_differential_eq_zero (m : ℕ) :
    Bor1.identityTangentMorphismLinearMap ((reeMorphism (F := F) m).comp (reeMorphism m)) = 0 := by
  have hs : (Bor1.identityTangentMorphismLinearMap (ExceptionalMorphism.morphism (F := F))) ^ 2 = 0 := by
    have h := frobenius_differential_eq_zero (F := F)
    rw [← ExceptionalMorphism.morphism_square, Bor1.identityTangentMorphismLinearMap_comp] at h
    exact h
  rw [Bor1.identityTangentMorphismLinearMap_comp]
  change (Bor1.identityTangentMorphismLinearMap (powerMorphism (F := F) (2 * m + 1))).comp
    (Bor1.identityTangentMorphismLinearMap (powerMorphism (F := F) (2 * m + 1))) = 0
  rw [powerMorphism_differential]
  change (Bor1.identityTangentMorphismLinearMap (ExceptionalMorphism.morphism (F := F))) ^ (2 * m + 1) *
    (Bor1.identityTangentMorphismLinearMap ExceptionalMorphism.morphism) ^ (2 * m + 1) = 0
  rw [← pow_add]
  exact pow_eq_zero_of_le (by omega) hs

public theorem centralizer_map (m : ℕ) (x : SourceFixedPoints.fixedGroup (F := F) m)
    (a : Variety.Point (pointCentralizer (x : PointGroup F)).carrierVariety) :
    ((reeMorphism m).comp (pointCentralizer (x : PointGroup F)).inclusion).onPoints a ∈
      (pointCentralizer (x : PointGroup F)).toSubgroup := by
  let C := pointCentralizer (x : PointGroup F)
  have ha : C.inclusion.onPoints a * (x : PointGroup F) = (x : PointGroup F) * C.inclusion.onPoints a :=
    Subgroup.mem_centralizer_singleton_iff.mp (C.pointEquiv a).property
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := congrArg (reeMorphism m).onPoints ha
  change (reeMorphism m).onPoints (C.inclusion.onPoints a) * (x : PointGroup F) =
    (x : PointGroup F) * (reeMorphism m).onPoints (C.inclusion.onPoints a)
  simpa only [map_mul, reeMorphism_fixed] using h

/-- The odd Ree morphism restricts to the original fixed point's centralizer. -/
@[expose] public noncomputable def centralizerRestriction (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m) :
    Morphism (pointCentralizer (x : PointGroup F)).carrierVariety
      (pointCentralizer (x : PointGroup F)).carrierVariety :=
  ((reeMorphism m).comp (pointCentralizer (x : PointGroup F)).inclusion).codRestrictClosedSubgroup
    (pointCentralizer (x : PointGroup F)) (centralizer_map m x)

public theorem centralizerRestriction_inclusion_apply (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m)
    (a : Variety.Point (pointCentralizer (x : PointGroup F)).carrierVariety) :
    (pointCentralizer (x : PointGroup F)).inclusion.onPoints ((centralizerRestriction m x).onPoints a) =
      (reeMorphism m).onPoints ((pointCentralizer (x : PointGroup F)).inclusion.onPoints a) :=
  Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _

/-- Bijectivity of the actual restriction follows by lifting through the ambient
point bijection and reflecting commutation. -/
public theorem centralizerRestriction_bijective (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m) :
    Function.Bijective (centralizerRestriction m x).onPoints := by
  let C := pointCentralizer (x : PointGroup F)
  have hσ := reeMorphism_bijective (F := F) m
  constructor
  · intro a b hab
    apply C.inclusion_injective
    apply hσ.injective
    rw [← centralizerRestriction_inclusion_apply, ← centralizerRestriction_inclusion_apply]
    exact congrArg C.inclusion.onPoints hab
  · intro a
    obtain ⟨b, hb⟩ := hσ.surjective (C.inclusion.onPoints a)
    have hbC : b ∈ C.toSubgroup := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      change b * (x : PointGroup F) = (x : PointGroup F) * b
      apply hσ.injective
      have ha : C.inclusion.onPoints a * (x : PointGroup F) = (x : PointGroup F) * C.inclusion.onPoints a :=
        Subgroup.mem_centralizer_singleton_iff.mp (C.pointEquiv a).property
      simpa only [map_mul, hb, reeMorphism_fixed] using ha
    refine ⟨C.pointEquiv.symm ⟨b, hbC⟩, C.inclusion_injective ?_⟩
    rw [centralizerRestriction_inclusion_apply]
    exact hb

/-- The literal inclusion transfers the square-zero differential to the
centralizer restriction. -/
public theorem centralizerRestriction_square_differential_eq_zero (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m) :
    Bor1.identityTangentMorphismLinearMap ((centralizerRestriction m x).comp (centralizerRestriction m x)) = 0 := by
  let C := pointCentralizer (x : PointGroup F)
  have heq : C.inclusion.comp ((centralizerRestriction m x).comp (centralizerRestriction m x)) =
      ((reeMorphism m).comp (reeMorphism m)).comp C.inclusion := by
    apply Morphism.ext
    funext a
    change C.inclusion.onPoints ((centralizerRestriction m x).onPoints ((centralizerRestriction m x).onPoints a)) =
      (reeMorphism m).onPoints ((reeMorphism m).onPoints (C.inclusion.onPoints a))
    rw [centralizerRestriction_inclusion_apply, centralizerRestriction_inclusion_apply]
  have hd := congrArg Bor1.identityTangentMorphismLinearMap heq
  rw [Bor1.identityTangentMorphismLinearMap_comp C.inclusion ((reeMorphism m).comp (reeMorphism m)),
    reeMorphism_square_differential_eq_zero, LinearMap.zero_comp] at hd
  rw [Bor1.identityTangentMorphismLinearMap_comp] at hd
  apply LinearMap.ext
  intro D
  apply Bor1.identityTangentMorphismLinearMap_inclusion_injective C
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using LinearMap.congr_fun hd D

/-- Lang's theorem on the actual Ree centralizer restriction. Connectedness is
the sole geometric premise left for the semisimple-centralizer source producer. -/
public theorem centralizerRestriction_lang_surjective (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m)
    (hC : Variety.IsConnected (pointCentralizer (x : PointGroup F)).carrierVariety) :
    Function.Surjective (langMorphism (centralizerRestriction m x)).toFun :=
  langMorphism_surjective_of_square_differential_eq_zero (centralizerRestriction m x)
    (centralizerRestriction_bijective m x).surjective hC
    (centralizerRestriction_square_differential_eq_zero m x)

/-- Correct an ambient conjugator inside its original connected centralizer;
the corrected conjugator belongs to the whole native Ree fixed group. -/
public theorem isConj_fixed_of_connected_centralizer (m : ℕ)
    (x y : SourceFixedPoints.fixedGroup (F := F) m)
    (hC : Variety.IsConnected (pointCentralizer (x : PointGroup F)).carrierVariety)
    (hxy : IsConj (x : PointGroup F) (y : PointGroup F)) : IsConj x y := by
  let ψ : Monoid.End (PointGroup F) := ExceptionalMorphism.morphism.onPoints
  apply Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.isConj_fixed_of_centralizer_lang
    (ψ ^ (2 * m + 1)) x y ?_ hxy
  intro a ha
  let C := pointCentralizer (x : PointGroup F)
  let aC := C.pointEquiv.symm ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr ha⟩
  obtain ⟨c, hc⟩ := centralizerRestriction_lang_surjective m x hC aC
  refine ⟨C.inclusion.onPoints c, Subgroup.mem_centralizer_singleton_iff.mp (C.pointEquiv c).property, ?_⟩
  have h := congrArg C.inclusion.onPoints hc
  rw [langMorphism_apply, map_inv] at h
  change C.inclusion.onPoints (c * ((centralizerRestriction m x).onPoints c)⁻¹) = a at h
  rw [map_mul, map_inv, centralizerRestriction_inclusion_apply, reeMorphism_onPoints] at h
  exact h

/-- The literal finite Ree consumer, preserving the original coefficient map. -/
public theorem isConj_model_of_connected_centralizer (m : ℕ) (f : CoefficientField m →+* F)
    (x y : Model m)
    (hC : Variety.IsConnected (pointCentralizer (modelEmbedding f x)).carrierVariety)
    (hxy : IsConj (modelEmbedding f x) (modelEmbedding f y)) : IsConj x y := by
  let e := SourceFixedPoints.modelEquiv m f
  have h := isConj_fixed_of_connected_centralizer m (e x) (e y) hC hxy
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
