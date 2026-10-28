module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HigmanSims
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action

/-!+# The two intrinsic obligations in the HS case

The input configuration retains the actual ambient component, its layer
closure, and the faithful action. It does not require L to be a component of
the centralizer of every nonidentity element of E: that hypothesis is used
only after the witnesses have been constructed.

The two outstanding calculations have distinct conclusions. One selects
fixed subgroups in the quotient action; the other identifies layers of fixed
subgroups in the covering group. Neither is asserted by these definitions.
In particular an isomorphism of a quotient centralizer is not an isomorphism
of a covering-group centralizer.

Source: Aschbacher–Smith, 16.3.5, printed p.1179 / PDF p.1196,
using 16.1.2, 16.1.5(10), 16.1.7(3h), and the cover facts in I.2.2(5).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open Subgroup Theory.GroupTheory
open OtherPreliminaries.JankoTwoHigmanSims
universe u
variable {G : Type u} [Group G]

/-- The hypotheses available before the parent applies its all-elements
component hypothesis. Every action is the actual ambient conjugation action. -/
structure Configuration [Finite G] (𝒦 : GroupClass.{u})
    (E L I : Subgroup G) (a i : G) : Prop where
  source : Hypothesis1611 𝒦 G
  setup : ComponentTransfer.Setup a i L
  actor_mem : a ∈ E
  closure_eq : I = ComponentTransfer.layerClosure (involutionCentralizer i) L
  component : IsCentralizerComponent i I
  proper : L < I
  relative_component : Theory.GroupTheory.IsComponentIn L (I ⊓ involutionCentralizer a)
  commutator_eq : ⁅I, zpowers a⁆ = I
  proper_models : CounterexampleGeometry.CoveredPersistence.ProperModels L I
  centralizes : E ≤ centralizer (L : Set G)
  centralizes_i : E ≤ involutionCentralizer i
  card : Nat.card E = 4
  normalizes : E ≤ normalizer (I : Set G)
  faithful : Function.Injective (inducedAction E I normalizes)
  core_ne : pCore 2 I ≠ ⊥
  calculation : ActionCalculation L I proper.le
  elementary : IsElementaryAbelian 2 E
  four_model : Nonempty (E ≃* E4)
  full_action : (inducedAction E I normalizes).range =
    centralizer ((inducedAction L I (proper.le.trans I.le_normalizer)).range : Set (MulAut I))

/-- The canonical quotient projection followed by the specified HS isomorphism. -/
def modelProjection (I : Subgroup G) (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    I →* Sporadic.LeechRelated.HS.Carrier :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))

/-- The action of Aut(I) on the specified quotient model. -/
def modelAction (I : Subgroup G) (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    MulAut I →* MulAut Sporadic.LeechRelated.HS.Carrier :=
  (MulAut.congr e).toMonoidHom.comp (pCore 2 I).quotientAut

/-- The actual E-action on HS, through I/O₂(I). -/
def quotientAction (E I : Subgroup G) (hn : E ≤ normalizer (I : Set G))
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    E →* MulAut Sporadic.LeechRelated.HS.Carrier :=
  (modelAction I e).comp (inducedAction E I hn)

/-- Selection of the two different rows of the quotient centralizer table.
This is an obligation about elements of the given E, not arbitrary model actors. -/
def QuotientFixedTypes (E I : Subgroup G) (hn : E ≤ normalizer (I : Set G))
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) : Prop :=
  ∃ s t : E, orderOf s = 2 ∧ orderOf t = 2 ∧
    Nonempty ((quotientAction E I hn e s).fixedSubgroup ≃* S8) ∧
    Nonempty ((quotientAction E I hn e t).fixedSubgroup ≃* C2 × MulAut A6)

/-- The individual covering-group layer calculations, for each involutory
automorphism. This does not select an element of E or assert the calculation. -/
def CoverLayerIdentification (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) : Prop :=
  ∀ r : MulAut I, orderOf r = 2 →
    (Nonempty ((modelAction I e r).fixedSubgroup ≃* S8) →
      Nonempty (componentLayer r.fixedSubgroup ≃* A8)) ∧
    (Nonempty ((modelAction I e r).fixedSubgroup ≃* C2 × MulAut A6) →
      Nonempty (componentLayer r.fixedSubgroup ≃* A6))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
