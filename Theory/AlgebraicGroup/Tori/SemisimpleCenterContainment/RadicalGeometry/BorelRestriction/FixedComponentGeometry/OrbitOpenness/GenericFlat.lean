module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.OrbitOpenness.GenericFlat.Schemes
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.ConnectedPreimage

/-!
# A nonempty flat patch for the complete Borel-model orbit

The connected group scheme is integral. Surjectivity of its actual orbit
morphism makes the reduced model target irreducible and therefore integral.
The generic source-patch theorem then applies to this morphism of geometric
varieties. In particular, separability and smoothness are not needed.

This is the flatness input to the homogeneous-quotient argument for connected
inverse images in Borel, *Linear Algebraic Groups*, §11.15
(`refs/KGroup/Bor1/Chapter4.tex`). Translation and the final openness assembly
are supplied by the separate `OrbitOpenness` modules.
-/

set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

universe u

namespace Theory.AlgebraicGroup.Variety.Geometric

/-- A dominant morphism of integral geometric varieties is flat on a nonempty
open subscheme of its source. -/
public theorem Morphism.exists_nonempty_flat_patch
    {k : Type u} [Field k] {V W : Geometric k}
    [AlgebraicGeometry.IsIntegral V.toScheme] [AlgebraicGeometry.IsIntegral W.toScheme]
    (f : Morphism V W) (hf : DenseRange f.hom) :
    ∃ U : V.toScheme.Opens, (U : Set V.toScheme).Nonempty ∧ Flat (U.ι ≫ f.hom) := by
  letI : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  letI : LocallyOfFiniteType f.hom := locallyOfFiniteType_of_comp f.hom W.structureMap
  letI : IsLocallyNoetherian W.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian W.structureMap
  exact f.hom.exists_nonempty_flat_patch hf

end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Variety.Geometric

/-- The literal Borel-model orbit morphism has a nonempty flat source patch
when the ambient algebraic group is connected. -/
public theorem modelOrbit_exists_flat_patch
    {k : Type u} [Field k] [IsAlgClosed k]
    {H : Variety k} [AlgebraicGroup H] {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) :
    ∃ U : (ofAffine H).toScheme.Opens,
      (U : Set (ofAffine H).toScheme).Nonempty ∧
        Flat (U.ι ≫ (M.action.orbitMorphismAt (modelBasePoint M)).hom) := by
  letI : IrreducibleSpace (ofAffine H).toScheme :=
    ofAffine_isIrreducible_of_isConnected H hH
  letI : AlgebraicGeometry.IsIntegral (ofAffine H).toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  letI : IrreducibleSpace M.variety.toScheme :=
    (modelOrbit_surjective M).irreducibleSpace
      (M.action.orbitMorphismAt (modelBasePoint M)).hom.continuous
  letI : AlgebraicGeometry.IsIntegral M.variety.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  exact (M.action.orbitMorphismAt (modelBasePoint M)).exists_nonempty_flat_patch
    (modelOrbit_surjective M).denseRange

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
