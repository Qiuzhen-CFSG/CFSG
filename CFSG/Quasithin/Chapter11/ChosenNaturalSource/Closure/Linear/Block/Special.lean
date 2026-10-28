module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualConsequences
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity

/-!
# Special-factor inputs to the original exceptional and multiplicity arguments

The special factor has order q⁵. The original solvable residual fixes
exactly Z(U), its G₁-conjugate span K centralizes Z(U), and U/Z(U) is
elementary of rank 4n. The marked point-parabolic action supplies both
the natural residual containment and its fixed space; no specialness,
center, rank or residual-action conclusion is assumed.

The exact five facts feed the exceptional-K and multiplicity consumers
below. Their preceding source inputs remain with the outer assembly.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.782.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

/-- The exact five consumer inputs, from the original marked geometry. -/
theorem consumer_inputs
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card (SpecialFactor E) = (2 ^ E.input.field.degree) ^ 5 ∧
    E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E ∧
    E.K ≤ centralizer (closureCenter E : Set G) ∧
    IsElementaryAbelian 2 (CentralQuotient E) ∧
    Group.rank (CentralQuotient E) = 4 * E.input.field.degree :=
  ⟨specialFactor_card E d hUT hf hc,
    source_closure_residual_fixed E d hUT hf hc,
    source_K_centralizes_center E d hUT hf hc,
    centralQuotient_elementary E d hUT hf,
    centralQuotient_rank E d hUT hf hc⟩

/-- Apply the special calculations to the original exceptional-K consumer. -/
theorem K_eq_pointResidual
    {κ : GroupClass} (hG₁ : IsSQTK κ E.G₁) (hK : Source.NormalComponentIn E.G₁ E.K)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X) : E.K = E.L₁ := by
  let := centralQuotient_elementary E d hUT hf
  exact Exceptional.K_eq_pointResidual E d hG₁ hK hUT
    (source_closure_residual_fixed E d hUT hf hc)
    (source_K_centralizes_center E d hUT hf hc)
    (centralQuotient_rank E d hUT hf hc) h htriangle

open LocalGeometry in
/-- Apply the proved special-factor order to the original multiplicity consumer. -/
theorem multiplicity_source_conclusions
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (b : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (b.space 0))
    (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (b.space 2))
    (hsum : ∃ r : ℕ, Nonempty (ActionEquiv (Multiplicity.action E f hK)
      (repeated (linearNatural E.input.field 2) r))) :
    let hseed := Multiplicity.seed_eq E m b hthree
    E.V₃ = V ∧ E.U = E.W ∧
    Nonempty (ActionEquiv (Multiplicity.action E f hK)
      (repeated (linearNatural E.input.field 2) 2)) ∧
    Nonempty (ActionEquiv (Multiplicity.pointAction E f hseed hK)
      (repeated (linearNatural E.input.field 2) 2)) ∧
    Nonempty (Outside.NaturalPair E) ∧
    Nat.card E.W = (2 ^ E.input.field.degree) ^ 5 ∧
    E.W = E.K.pCoreIn 2 ∧ E.W = E.L₁.pCoreIn 2 ∧ E.W ≤ L ∧
    E.W ⊓ centralizer (L : Set G) = ⊥ ∧ L.pCoreIn 2 = V ∧
    sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
  Multiplicity.source_conclusions E d hUT hf hc f hK m b hpoint hthree hsum
    (specialFactor_card E d hUT hf hc)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
