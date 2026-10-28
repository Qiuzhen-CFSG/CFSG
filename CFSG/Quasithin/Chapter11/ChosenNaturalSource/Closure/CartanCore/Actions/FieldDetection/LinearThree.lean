module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Lifting
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl

/-!
# The graph-compatible PSL₃ torus on the original quotient

The diagonal torus diag(a,1,a⁻¹) is faithful in PSL₃ in characteristic two
and is fixed by the opposition graph automorphism. Consequently a field
actor, also when followed by that graph automorphism, moves its parameter
exactly by the coefficient automorphism. Transport through a genuine marking
of J/O₂(J) supplies the common field-torus section and its odd Borel movement.

The construction of the odd-degree subfield J and the normalizer lifts is
still explicit. This theorem does not classify the original component or
assert the simultaneous Sylow/subfield arrangement.
Source: Aschbacher--Smith 11.5.6(3), printed p.781, graph-automorphism case.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open Matrix.PSL3.CartanActions.RootTorusControl Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection

/-- The two standard actors have the same coefficient action on the root torus. -/
def linearThreeActor (F : BinaryField) (σ : F.Carrier ≃+* F.Carrier) (graph : Bool) :
    MulAut PSL(3, F.Carrier) :=
  if graph then fieldAction F.Carrier σ * oppositionGraph F.Carrier
  else fieldAction F.Carrier σ

theorem linearThreeActor_torus (F : BinaryField) (σ : F.Carrier ≃+* F.Carrier)
    (graph : Bool) (u : F.Carrierˣ) :
    linearThreeActor F σ graph (rootTorus F.Carrier u) =
      rootTorus F.Carrier (Units.map σ.toMonoidHom u) := by
  cases graph <;> simp [linearThreeActor, MulAut.mul_apply,
    graph_rootTorus, field_rootTorus]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- An actual PSL₃ marking and its compatible normalizer lifts produce the
field-torus input, retaining the possible opposition graph actor. -/
def linearThreeSection (J : Subgroup G) (hJ : J ≤ E.Y) (F : BinaryField)
    (e : (J ⧸ pCore 2 J) ≃* PSL(3, F.Carrier))
    (a : normalizer (J : Set G)) (ha : (a : G) ∈ E.X)
    (σ : F.Carrier ≃+* F.Carrier) (hσ : σ ≠ 1) (graph : Bool)
    (hact : ∀ z, e (coreQuotientAction J a z) = linearThreeActor F σ graph (e z))
    (hlift : ∀ u, ∃ j : J, (j : G) ∈ normalizer (T : Set G) ∧
      e (QuotientGroup.mk' (pCore 2 J) j) = rootTorus F.Carrier u) :
    FieldTorusSection E where
  J := J
  le_Y := hJ
  field := F
  torus := e.symm.toMonoidHom.comp (rootTorus F.Carrier)
  injective := e.symm.injective.comp (rootTorus_injective F.Carrier)
  actor := a
  actor_mem := ha
  coefficient := σ
  nontrivial := hσ
  action u := by
    apply e.injective
    simpa only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulEquiv.apply_symm_apply, linearThreeActor_torus] using
      hact (e.symm (rootTorus F.Carrier u))
  lifts u := by
    obtain ⟨j, hj, he⟩ := hlift u
    exact ⟨j, hj, e.injective (by simpa using he)⟩

/-- The original-geometry consumer of the graph-compatible torus calculation. -/
theorem borel_movement_of_linearThree (J : Subgroup G) (hJ : J ≤ E.Y) (F : BinaryField)
    (e : (J ⧸ pCore 2 J) ≃* PSL(3, F.Carrier))
    (a : normalizer (J : Set G)) (ha : (a : G) ∈ E.X)
    (σ : F.Carrier ≃+* F.Carrier) (hσ : σ ≠ 1) (graph : Bool)
    (hact : ∀ z, e (coreQuotientAction J a z) = linearThreeActor F σ graph (e z))
    (hlift : ∀ u, ∃ j : J, (j : G) ∈ normalizer (T : Set G) ∧
      e (QuotientGroup.mk' (pCore 2 J) j) = rootTorus F.Carrier u) :
    E.BorelMovement :=
  (linearThreeSection E J hJ F e a ha σ hσ graph hact hlift).borel_movement

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection
