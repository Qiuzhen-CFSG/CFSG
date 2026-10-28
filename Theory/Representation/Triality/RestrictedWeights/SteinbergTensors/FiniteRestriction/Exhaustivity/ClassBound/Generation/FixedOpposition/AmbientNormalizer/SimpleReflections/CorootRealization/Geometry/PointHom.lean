module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison

/-!
# Point maps for actual simple D4 root pairs

This intermediate interface separates the rank-one group relations from
regularity. Both root parametrizations are chosen together with a homomorphism
on SL₂ points that carries its upper and lower curves to them. No diagonal
containment, coroot identity, reflection representative, or regularity is
assumed here. Existence of these data is a geometric obligation, not a field
of `FiniteRestriction.Geometry`.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and the formulas preceding
Theorem 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`; Steinberg, Section 6,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Compatible choices for the two actual root curves and their SL₂ point
map. Regularity of the point map is a separate assertion. -/
structure SimpleRootSL2PointHom (S : Geometry K) (i : Fin 4) where
  plus : OneParameterParametrization
    (S.roots.rootSubgroup (S.simpleRoot i).val).carrierVariety
  minus : OneParameterParametrization
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).carrierVariety
  map : Variety.Point (slVariety k 2) →*
    Variety.Point (oppositePairGeneratedSubgroup
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).carrierVariety
  upper : ∀ s : Variety.Point (KPlus k),
    (oppositePairPlusMorphism
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).onPoints
        (plus.hom.onPoints s) = map (standardSL2UpperMorphism.onPoints s)
  lower : ∀ s : Variety.Point (KPlus k),
    (oppositePairMinusMorphism
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).onPoints
        (minus.hom.onPoints s) = map (standardSL2LowerMorphism.onPoints s)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
