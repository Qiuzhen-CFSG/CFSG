module

public import Theory.AlgebraicGroup.Morphism.SL2RootRegularity
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointHom

/-!
# Regularity of the simple-root SL₂ point maps

A compatible SL₂ point homomorphism for an actual opposite simple-root pair
is regular: its two root curves are the chosen algebraic parametrizations
followed by the inclusions into the generated subgroup. Apply the general
SL₂ root-curve regularity theorem to these curves. Existence of the compatible
point homomorphism remains a separate mathematical input.

Sources: GLS3, §1.12, `refs/KGroup/GLS3/Chapter1.tex`; Steinberg, §6,
especially the big-cell description (6.2)(c),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The compatible point map for a simple-root pair is an algebraic-group
morphism, with exactly the supplied map on points. -/
theorem SimpleRootSL2PointHom.exists_morphism {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2PointHom S i) :
    ∃ F : Morphism (slVariety k 2) (oppositePairGeneratedSubgroup
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).carrierVariety,
      F.onPoints = C.map := by
  apply exists_sl2Morphism_of_regular_rootCurves C.map
    ((oppositePairPlusMorphism _ _).comp C.plus.hom)
    ((oppositePairMinusMorphism _ _).comp C.minus.hom)
  · intro s
    exact (C.upper s).symm
  · intro s
    exact (C.lower s).symm

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
