module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.FixedSpace

/-!
# Independent geometric and representation inputs for the Leech local A₅

`Geometry` retains the actual subgroup, its D₁₀ centralization, the common
reflection and cubic torus, and one actual scalar-class involution. A₅ fusion
extends this single conjugacy witness to every local involution.
`FactorAction` asks only for a factorization of its literal coordinate action.
Neither input assumes faithfulness or surjectivity of the two projections;
`SourceConstruction` proves both from simplicity and the common reflection.

These are uninhabited construction contracts, not source existence theorems.
The geometric producer must supply Lemmas 47.2 and 48.8 in this Leech quotient,
while the representation producer supplies the linear-centralizer calculation
in Lemma 49.5 of Aschbacher, *Sporadic Groups* (1994), pp.283–284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

/-- Source local geometry, before identifying the action with its linear factors.
The common reflection and torus are marked by their actual coordinate actions;
no equality with an arbitrary choice of `L.swap` is presumed. -/
structure Geometry (L : LongFrame) where
  subgroup : Subgroup LeechCentralQuotient
  alternating : subgroup ≃* alternatingGroup (Fin 5)
  mem : ∀ a : subgroup, (a : LeechCentralQuotient) ∈ centralizerI
  centralizes : ∀ (a : subgroup) d, Commute (a : LeechCentralQuotient) (dihedralLift L d)
  reflection : subgroup
  reflection_action : ∀ v,
    quotientModTwoRepresentation (reflection : LeechCentralQuotient) (L.coordinates v) =
      L.coordinates (pairRepresentation (flip, flip) v)
  cubic : Fˣ → subgroup
  cubic_action : ∀ t v,
    quotientModTwoRepresentation (cubic t : LeechCentralQuotient) (L.coordinates v) =
      L.coordinates (pairRepresentation (torus t, (torus t)⁻¹) v)
  scalar_witness : ∃ a : subgroup, orderOf a = 2 ∧
    IsConj (a : LeechCentralQuotient) scalarInvolution

/-- The factorization still to be proved from the literal dihedral centralizer.
Faithfulness and surjectivity of both projections are conclusions below. -/
structure FactorAction {L : LongFrame} (G : Geometry L) where
  hom : G.subgroup →* (SL(2,F) × SL(2,F))
  on_action : ∀ (a : G.subgroup) v,
    quotientModTwoRepresentation (a : LeechCentralQuotient) (L.coordinates v) =
      L.coordinates (pairRepresentation (hom a) v)

variable {L : LongFrame} {G : Geometry L}

/-- One scalar-class involution determines the class of every involution
of the local A₅ in the actual quotient. -/
theorem Geometry.involution_class (G : Geometry L) (a : G.subgroup)
    (ha : orderOf a = 2) : IsConj (a : LeechCentralQuotient) scalarInvolution := by
  obtain ⟨b, hb, hc⟩ := G.scalar_witness
  have h : IsConj (G.alternating a) (G.alternating b) :=
    alternatingGroup.five_involutions_isConj _ _
      (by rw [G.alternating.orderOf_eq, ha]) (by rw [G.alternating.orderOf_eq, hb])
  have h' : IsConj a b := by
    have hi := G.alternating.symm.toMonoidHom.map_isConj h
    change IsConj (G.alternating.symm (G.alternating a))
      (G.alternating.symm (G.alternating b)) at hi
    simpa only [MulEquiv.symm_apply_apply] using hi
  exact (G.subgroup.subtype.map_isConj h').trans hc

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
