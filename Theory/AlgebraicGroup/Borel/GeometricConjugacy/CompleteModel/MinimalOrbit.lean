module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.NonAffineFormula

/-!
# Maximal-dimensional stabilizers have closed orbits

For the actual orbit map of a possibly disconnected algebraic group, rational
scheme fibres have the topology of the reduced point stabilizer. Every nonempty
open in such a fibre has the stabilizer dimension. Applying the non-affine fibre
dimension formula proves the orbit–stabilizer dimension relation. All orbit
components have the same dimension, so the relation holds componentwise too.

A maximal-dimensional stabilizer therefore gives a minimal-dimensional orbit.
The boundary argument keeps the selected point: a rational point in its boundary
would have a strictly smaller orbit, a contradiction. The conclusion concerns
the actual scheme-point range of the original orbit morphism. No connectedness
or separability hypothesis is needed.

Source: Borel, *Linear Algebraic Groups*, §§1.8 and 11.1,
`refs/KGroup/Bor1/Chapter1.tex` and `refs/KGroup/Bor1/Chapter4.tex`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

/-- The orbit–stabilizer dimension formula, including disconnected groups and inseparable orbit maps. -/
public theorem orbit_stabilizer_dimension_formula :
    (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) =
      dimension (A.orbitSubvariety x).toGeometric +
        (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) := by
  let : Nonempty (ofAffine G).toScheme :=
    ⟨((affinePointEquiv G).symm 1).1 (IsLocalRing.closedPoint k)⟩
  rw [← MinimalOrbit.ofAffine_group_dimension G]
  exact MinimalOrbit.dimension_eq_add_of_homogeneous_fibers
    (A.toOrbitSubvariety x) (A.toOrbitSubvariety_surjective x)
    (ofAffine_group_closedPoint_transitive G) (A.orbitSubvariety_closedPoint_transitive x)
    (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety))
    (A.toOrbitSubvariety_fiber_nonemptyOpen_dimension x)

/-- Each orbit component satisfies the same dimension formula with the full point stabilizer. -/
public theorem orbitComponent_stabilizer_dimension_formula
    (Z : IrreducibleComponent (A.orbitSubvariety x).toGeometric) :
    (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) =
      dimension (irreducibleComponentSubvariety (A.orbitSubvariety x).toGeometric Z).toGeometric +
        (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) := by
  rw [A.orbitSubvariety_component_dimension]
  exact A.orbit_stabilizer_dimension_formula x

/-- An orbit whose stabilizer has maximal dimension is closed (Borel, §11.1). -/
public theorem isClosed_orbitMorphismAt_range_of_maximal_stabilizer_dimension
    (hmax : ∀ y : Point X,
      Variety.dimension (A.pointStabilizer y).carrierVariety ≤
        Variety.dimension (A.pointStabilizer x).carrierVariety) :
    IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
  apply A.isClosed_orbitMorphismAt_range_of_minimal_dimension x
  intro y
  have hnat : Cardinal.toNat (Variety.dimension (A.pointStabilizer y).carrierVariety) ≤
      Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) :=
    (Cardinal.toNat_le_iff_le_of_lt_aleph0
      (variety_dimension_lt_aleph0 (A.pointStabilizer y).carrierVariety)
      (variety_dimension_lt_aleph0 (A.pointStabilizer x).carrierVariety)).mpr (hmax y)
  have hs : (Cardinal.toNat (Variety.dimension (A.pointStabilizer y).carrierVariety) : WithBot ℕ∞) ≤
      (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) := by
    exact_mod_cast hnat
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := Cardinal.toNat
    (Variety.dimension (A.pointStabilizer y).carrierVariety))).mp
  calc
    dimension (A.orbitSubvariety x).toGeometric +
        (Cardinal.toNat (Variety.dimension (A.pointStabilizer y).carrierVariety) : WithBot ℕ∞) ≤
      dimension (A.orbitSubvariety x).toGeometric +
        (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) :=
      add_le_add le_rfl hs
    _ = (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) :=
      (A.orbit_stabilizer_dimension_formula x).symm
    _ = dimension (A.orbitSubvariety y).toGeometric +
        (Cardinal.toNat (Variety.dimension (A.pointStabilizer y).carrierVariety) : WithBot ℕ∞) :=
      A.orbit_stabilizer_dimension_formula y

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
