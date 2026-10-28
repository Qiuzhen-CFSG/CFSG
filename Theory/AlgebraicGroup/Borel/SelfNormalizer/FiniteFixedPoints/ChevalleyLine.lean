module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.CharacterKernel
public import Theory.AlgebraicGroup.RightTranslation.ExteriorRational
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
# The normalizer Chevalley vector and its regular orbit map

The exterior Chevalley representation supplies a nonzero vector whose full
line stabilizer is the literal normalizer of the Borel. Its rationality and
regular character are proved, and the finite fixed-torus character calculation
shows that the Borel fixes the vector. Exterior matrix coefficients construct
the genuine affine orbit morphism on `G` and prove its right B-invariance.
This last property does not by itself assert regular descent to a complete
model of `G/B`.

Source: Borel, *Linear Algebraic Groups*, §§5.1 and 11.16(iii),
`refs/KGroup/Bor1/Chapter4.tex`, line 229.
-/

universe u

namespace Theory.AlgebraicGroup.BorelSelfNormalizer
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

public noncomputable abbrev NormalizerChevalleySpace (B : ClosedSubgroup G) :=
  ⋀[k]^B.normalizer.rightTranslateVanishingTopWedgeData.degree
    B.normalizer.rightTranslateVanishingSpan

@[expose]
public noncomputable def normalizerChevalleyRepresentation (B : ClosedSubgroup G) :
    RationalRepresentation G (NormalizerChevalleySpace B) :=
  B.normalizer.rightTranslateVanishingExteriorRationalRepresentation

@[expose]
public noncomputable def normalizerChevalleyVector (B : ClosedSubgroup G) :
    NormalizerChevalleySpace B :=
  B.normalizer.rightTranslateVanishingPluckerVector

public theorem normalizerChevalleyRepresentation_isRational (B : ClosedSubgroup G) :
    IsRationalRepresentation (normalizerChevalleyRepresentation B) :=
  B.normalizer.rightTranslateVanishingExteriorRationalRepresentation_isRational

omit [IsAlgClosed k] in
public theorem normalizerChevalleyVector_ne_zero (B : ClosedSubgroup G) :
    normalizerChevalleyVector B ≠ 0 :=
  B.normalizer.rightTranslateVanishingPluckerVector_ne_zero

omit [IsAlgClosed k] in
public theorem normalizerChevalleyLine_stabilizer (B : ClosedSubgroup G) (g : Variety.Point G) :
    ((normalizerChevalleyRepresentation B).action g).1 (normalizerChevalleyVector B) ∈
      k ∙ normalizerChevalleyVector B ↔ g ∈ B.normalizer.toSubgroup := by
  rw [show ((normalizerChevalleyRepresentation B).action g).1 (normalizerChevalleyVector B) =
      exteriorPower.map B.normalizer.rightTranslateVanishingTopWedgeData.degree
        (B.normalizer.rightTranslateVanishingSpanGeneralLinear g).toLinearEquiv.toLinearMap
        (normalizerChevalleyVector B) from
      B.normalizer.rightTranslateVanishingExteriorGeneralLinear_apply g _]
  exact B.normalizer.chevalleyPluckerLine_stabilizer_iff g

omit [IsAlgClosed k] in
public theorem normalizerChevalleyVector_generatesInvariantLine (B : ClosedSubgroup G) :
    GeneratesInvariantLine (normalizerChevalleyRepresentation B) B.normalizer
      (normalizerChevalleyVector B) := by
  refine ⟨normalizerChevalleyVector_ne_zero B, ?_⟩
  intro g hg
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((normalizerChevalleyLine_stabilizer B g).mpr hg)
  exact ⟨c, hc.symm⟩

/-- The actual Chevalley line carries a regular character of the full normalizer. -/
public theorem normalizerChevalleyLine_character (B : ClosedSubgroup G) :
    ∃! χ : TorusCharacter B.normalizer.carrierVariety,
      IsWeightVector (normalizerChevalleyRepresentation B) B.normalizer
        (normalizerChevalleyVector B) χ :=
  invariantLine_torusWeight_existsUnique_public _
    (normalizerChevalleyRepresentation_isRational B) _ _
    (normalizerChevalleyVector_generatesInvariantLine B)

/-- The Chevalley vector is fixed by B in Borel 11.16(iii). -/
public theorem normalizerChevalleyVector_fixed_by_borel
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (hnT : n ∈ T.normalizer.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite) :
    ∀ b : Variety.Point G, b ∈ B.toSubgroup →
      ((normalizerChevalleyRepresentation B).action b).1 (normalizerChevalleyVector B) =
        normalizerChevalleyVector B :=
  borel_fixes_invariantLine_of_finite_fixedPoints B T hB hT hTB n hnB hnT hfixed
    _ (normalizerChevalleyRepresentation_isRational B) _
    (normalizerChevalleyVector_generatesInvariantLine B)

end Theory.AlgebraicGroup.BorelSelfNormalizer

namespace Theory.AlgebraicGroup.BorelSelfNormalizer
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

@[expose]
public noncomputable def normalizerChevalleyBasis (B : ClosedSubgroup G) :
    Module.Basis (ULift.{u} (Fin (Fintype.card B.normalizer.rightTranslateVanishingExteriorIndex)))
      k (NormalizerChevalleySpace B) :=
  B.normalizer.rightTranslateVanishingExteriorBasis.reindex Equiv.ulift.symm

public noncomputable abbrev NormalizerChevalleyAffineSpace (B : ClosedSubgroup G) : Variety k :=
  affineSpaceVariety k
    (ULift.{u} (Fin (Fintype.card B.normalizer.rightTranslateVanishingExteriorIndex)))

/-- The regular orbit morphism of the literal normalizer Chevalley vector. -/
@[expose]
public noncomputable def normalizerChevalleyOrbitMorphism (B : ClosedSubgroup G) :
    Variety.Morphism G (NormalizerChevalleyAffineSpace B) where
  toFun g := affineSpacePoint ((normalizerChevalleyBasis B).repr
    (((normalizerChevalleyRepresentation B).action g).1 (normalizerChevalleyVector B)))
  regular := by
    intro i
    let c := B.normalizer.rightTranslateVanishingExteriorLinearMatrixCoefficient
      ((normalizerChevalleyBasis B).coord i) (normalizerChevalleyVector B)
    obtain ⟨p, hp⟩ := c.representedBy
    refine ⟨p, fun g => ?_⟩
    rw [← hp g]
    exact (B.normalizer.rightTranslateVanishingExteriorLinearMatrixCoefficient_apply
      ((normalizerChevalleyBasis B).coord i) (normalizerChevalleyVector B) g).symm

omit [IsAlgClosed k] in
public theorem normalizerChevalleyOrbitMorphism_eq_iff (B : ClosedSubgroup G)
    (g h : Variety.Point G) :
    (normalizerChevalleyOrbitMorphism B).toFun g = (normalizerChevalleyOrbitMorphism B).toFun h ↔
      ((normalizerChevalleyRepresentation B).action g).1 (normalizerChevalleyVector B) =
        ((normalizerChevalleyRepresentation B).action h).1 (normalizerChevalleyVector B) := by
  constructor
  · intro heq
    apply (normalizerChevalleyBasis B).repr.injective
    ext i
    exact congrArg (fun x : Variety.Point (NormalizerChevalleyAffineSpace B) => x.val i) heq
  · intro heq
    exact congrArg (fun v => affineSpacePoint
      ((normalizerChevalleyBasis B).repr v)) heq

/-- Right B-invariance of the regular orbit map; geometric descent is a further step. -/
public theorem normalizerChevalleyOrbitMorphism_mul_borel
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (hnT : n ∈ T.normalizer.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite)
    (g b : Variety.Point G) (hb : b ∈ B.toSubgroup) :
    (normalizerChevalleyOrbitMorphism B).toFun (g * b) =
      (normalizerChevalleyOrbitMorphism B).toFun g := by
  apply (normalizerChevalleyOrbitMorphism_eq_iff B _ _).mpr
  rw [map_mul]
  change ((normalizerChevalleyRepresentation B).action g).1
    (((normalizerChevalleyRepresentation B).action b).1 (normalizerChevalleyVector B)) = _
  rw [normalizerChevalleyVector_fixed_by_borel B T hB hT hTB n hnB hnT hfixed b hb]

end Theory.AlgebraicGroup.BorelSelfNormalizer
