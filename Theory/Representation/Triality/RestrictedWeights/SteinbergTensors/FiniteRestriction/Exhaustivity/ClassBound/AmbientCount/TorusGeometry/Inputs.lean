module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Coordinates

/-!
# Geometric obligations for the actual D4 torus

These are separate intermediate contracts, not consequences asserted from
`Geometry`. `WeylGeometry` asks for the Weyl action on the actual torus, its
point reflection formula and ambient fusion. `PinnedTorusMaps` asks for actual
algebraic restrictions of the pinned maps and their simple-coroot equations.
The character equations are derived in `Coordinates` and `TorusGeometry`.

Semisimple containment remains a separate geometric obligation. Together these
inputs feed the conditional construction of `TorusData`; none assumes a class
count, a representation classification or a concrete algebraic-group carrier.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§6, 11 and the torus/Weyl
passage in the proof of 14.8(a).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual Weyl action and fusion statement, specified by a point formula
for its simple reflections. Existence remains a geometric proof obligation. -/
structure WeylGeometry (S : Geometry K) where
  action : MulAction Weyl (Variety.Point S.torus.carrierVariety)
  reflection_point : letI := action
    ∀ (i : Fin 4) (t : Variety.Point S.torus.carrierVariety),
      (RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)) • t =
        simpleReflection S i t
  conjugate_iff : letI := action
    ∀ t u : Variety.Point S.torus.carrierVariety,
      IsConj (S.torus.includePoint t) (S.torus.includePoint u) ↔ ∃ w : Weyl, w • t = u

/-- Algebraic torus restrictions with their simple-coroot equations. All
equations must be derived from the supplied ambient pinning in `Geometry`. -/
structure PinnedTorusMaps (S : Geometry K) where
  diagram : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety
  frobenius : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety
  diagram_ambient : ∀ t, S.torus.includePoint (diagram.onPoints t) =
    S.diagram.toMulEquiv (S.torus.includePoint t)
  frobenius_ambient : ∀ t, S.torus.includePoint (frobenius.onPoints t) =
    S.frobenius.onPoints (S.torus.includePoint t)
  diagram_coroot : ∀ (i : Fin 4) (z : Variety.Point (KMult k)),
    diagram.onPoints ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
      (S.roots.rootCocharacter (S.simpleRoot (typeD4DiagramPermutation i)).val).onPoints z
  frobenius_coroot : ∀ (i : Fin 4) (z : Variety.Point (KMult k)),
    frobenius.onPoints ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
      (S.roots.rootCocharacter (S.simpleRoot i).val).onPoints (z ^ 2)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
