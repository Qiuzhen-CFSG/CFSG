module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.ScalarLinearity
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.LinearCentralizer

/-!
# Factorization of the literal Leech local A₅ action

The actual Y operator recovers field linearity in any additive long frame.
Dihedral centralization preserves the literal fixed pair and forces the
remaining coordinates into two identical matrix blocks. Coefficient
extraction gives homomorphisms, and A₅ perfectness makes both determinants
one. This constructs the required factor action on every vector.

This theorem is conditional on the geometric input. The geometric producer
and `SourceConstruction` retain the unconditional source assembly, including
faithfulness and surjectivity of the projections.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
namespace Factorization

theorem geometry_perfect {L : LongFrame} (G : Geometry L) : Group.IsPerfect G.subgroup := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := G.alternating.symm.toMonoidHom)
    G.alternating.symm.surjective

def factorActionOfBlockForm {L : LongFrame} (G : Geometry L)
    (h : ∀ a v, localAction G a v = matrixAction (coefficients (localAction G a)) v) :
    FactorAction G := by
  let : Group.IsPerfect G.subgroup := geometry_perfect G
  exact
    { hom := specialLinearPair (localAction G) h
      on_action := fun a v => by rw [specialLinearPair_action, localAction_spec] }

end Factorization

/-- The source local A₅ acts through the two literal SL₂ factors. The only
input is the geometric source configuration, in its supplied additive frame. -/
theorem exists_factorAction {L : LongFrame} (G : Geometry L) : Nonempty (FactorAction G) := by
  refine ⟨Factorization.factorActionOfBlockForm G ?_⟩
  intro a v
  let f : (Fin 6 → F) →ₗ[F] (Fin 6 → F) :=
    { toFun := Factorization.localAction G a
      map_add' := (Factorization.localAction G a).toAdd.map_add
      map_smul' := Factorization.coordinateAction_smul L ⟨a.val, G.mem a⟩ }
  exact Factorization.linear_centralizer_blockForm f
    (Factorization.localAction_preserves_fixed G a)
    (Factorization.localAction_commutes G a) v

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
