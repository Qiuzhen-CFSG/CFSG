module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointHom
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.Diagonal

/-!
# Assembling actual simple-root SL₂ charts

Compatible regular SL₂ maps for the actual opposite-root pairs automatically
satisfy the diagonal-containment clause, by maximality of the ambient torus.
Consequently chart construction separates into compatible point-map existence
and regularity of that point map. The construction here discharges diagonal
containment; it does not assert either remaining existence theorem.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and the defining formulas of
Theorem 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`; Steinberg, Section 6,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A regular realization of the compatible point map supplies a full chart.
In particular the diagonal-containment field is proved, not supplied. -/
def SimpleRootSL2PointHom.chart_of_morphism {S : Geometry K} {i : Fin 4}
    (C : SimpleRootSL2PointHom S i)
    (f : Morphism (slVariety k 2) (oppositePairGeneratedSubgroup
      (S.roots.rootSubgroup (S.simpleRoot i).val)
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).carrierVariety)
    (hf : f.onPoints = C.map) : SimpleRootSL2Chart S i := by
  have hc : OppositePairSL2Compatible _ _ C.plus C.minus f := by
    constructor
    · apply Morphism.ext
      funext s
      change (oppositePairPlusMorphism _ _).onPoints (C.plus.hom.onPoints s) =
        f.onPoints (standardSL2UpperMorphism.onPoints s)
      rw [hf]
      exact C.upper s
    · apply Morphism.ext
      funext s
      change (oppositePairMinusMorphism _ _).onPoints (C.minus.hom.onPoints s) =
        f.onPoints (standardSL2LowerMorphism.onPoints s)
      rw [hf]
      exact C.lower s
  refine ⟨C.plus, C.minus, f, hc, ?_⟩
  apply hc.diagonal_mem_of_maximalTorus _ _ _ S.maximalTorus
    (S.roots.rootWeight (S.simpleRoot i).val)
    (S.realized.2.2.1 (S.simpleRoot i).val).2
  rw [← S.realized.2.2.2.1 (S.simpleRoot i).val]
  exact (S.realized.2.2.1 (S.roots.neg (S.simpleRoot i).val)).2

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
