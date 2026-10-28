module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.ConnectedPreimage
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.OrbitOpenness.GenericFlat
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.OrbitOpenness.Translation

/-!
# Openness of the Borel-model orbit morphism

The actual orbit map from a connected algebraic group to a complete Borel model
is open. The group scheme is integral, and its surjective image is irreducible,
so the reduced model target is integral as well. The generic flat-patch theorem
supplies a nonempty source-open subscheme on which the orbit morphism is flat.
Translation propagates openness to the whole source, including nonclosed scheme
points. Inseparable orbit maps are permitted throughout.

Applying the connected-fibre argument gives connectedness of inverse images of
connected closed subvarieties, with the exact reduced inverse-image convention
used in §11.15. The earlier conditional flat-patch interfaces are retained.

Source: Borel, *Linear Algebraic Groups*, §11.15,
`refs/KGroup/Bor1/Chapter4.tex`.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

/-- The actual complete Borel model has integral underlying scheme when the
ambient group is connected. -/
public theorem modelVariety_isIntegral {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) :
    AlgebraicGeometry.IsIntegral M.variety.toScheme := by
  letI : IrreducibleSpace (ofAffine H).toScheme :=
    ofAffine_isIrreducible_of_isConnected H hH
  letI : IrreducibleSpace M.variety.toScheme :=
    (modelOrbit_surjective M).irreducibleSpace
      (M.action.orbitMorphismAt (modelBasePoint M)).hom.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced M.variety.toScheme

/-- A single nonempty flat source patch suffices for the actual Borel-model
orbit morphism to send arbitrary source-open sets to target-open sets. -/
public theorem modelOrbit_isOpenMap_of_flat_patch {B : ClosedSubgroup H}
    (M : CompleteModel B) (U : (ofAffine H).toScheme.Opens)
    (hne : (U : Set (ofAffine H).toScheme).Nonempty)
    (hflat : Flat (U.ι ≫ (M.action.orbitMorphismAt (modelBasePoint M)).hom)) :
    IsOpenMap (M.action.orbitMorphismAt (modelBasePoint M)).hom :=
  M.action.orbitMorphismAt_isOpenMap_of_flat_patch (modelBasePoint M) U hne hflat

/-- The actual Borel-model orbit morphism sends every open subset of the group
scheme to an open subset of the target scheme. No separability is required. -/
public theorem modelOrbit_isOpenMap {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) :
    IsOpenMap (M.action.orbitMorphismAt (modelBasePoint M)).hom := by
  obtain ⟨U, hne, hflat⟩ := modelOrbit_exists_flat_patch M hH
  exact modelOrbit_isOpenMap_of_flat_patch M U hne hflat

/-- The flat patch discharges the openness premise in the connected-preimage
argument for the literal reduced inverse image of a closed subvariety. -/
public theorem componentPreimage_isConnected_of_flat_patch {B : ClosedSubgroup H}
    (M : CompleteModel B) (hB : IsBorelSubgroup B)
    (X : ClosedSubvariety M.variety) (hX : Variety.Geometric.IsConnected X.toGeometric)
    (U : (ofAffine H).toScheme.Opens)
    (hne : (U : Set (ofAffine H).toScheme).Nonempty)
    (hflat : Flat (U.ι ≫ (M.action.orbitMorphismAt (modelBasePoint M)).hom)) :
    Variety.Geometric.IsConnected (componentPreimage M X).toGeometric :=
  componentPreimage_isConnected_of_isOpenMap M hB X hX
    (modelOrbit_isOpenMap_of_flat_patch M U hne hflat)

/-- For a connected ambient group and a Borel stabilizer, the literal reduced
inverse image of a connected closed subvariety of the model is connected.
This discharges the orbit-map openness premise in the §11.15 argument. -/
public theorem componentPreimage_isConnected {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) (hB : IsBorelSubgroup B)
    (X : ClosedSubvariety M.variety) (hX : Variety.Geometric.IsConnected X.toGeometric) :
    Variety.Geometric.IsConnected (componentPreimage M X).toGeometric :=
  componentPreimage_isConnected_of_isOpenMap M hB X hX (modelOrbit_isOpenMap M hH)

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
