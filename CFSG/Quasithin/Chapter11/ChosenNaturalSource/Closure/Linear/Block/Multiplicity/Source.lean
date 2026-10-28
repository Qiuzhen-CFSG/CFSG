module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Order
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Core

/-!
# Multiplicity and original cores in the SL₃ branch of 11.5.7

The actual three-dimensional flag identifies V₃ with V and counts V₁.
The fixed-vector argument removes C_U(L), and the special-factor order
then counts U and its two natural summands. The fixed-free displacement
argument identifies the original solvable-residual two-core. Finally,
O₂(L)=V discharges the core premise of the source T_L splitting.

The natural-sum premise is exactly globalClosure_natural_sum from 11.5.5(3).
The earlier flag, marked G.2 hypothesis, core collapse, K=L₁ and the
special-factor order remain explicit source inputs. Their discharge is
retained by the SL₃ exceptional-block assembly owner. Both the intrinsic
ActionEquiv and the terminal consumer's NaturalPair are constructed here.
Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

theorem source_conclusions {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (f : E.ClosureFlag) (hK : E.K = E.L₁)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (b : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (b.space 0))
    (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (b.space 2))
    (hsum : ∃ r : ℕ, Nonempty (ActionEquiv (action E f hK)
      (repeated (linearNatural E.input.field 2) r)))
    (hspecial : Nat.card (SpecialFactor E) = (2 ^ E.input.field.degree) ^ 5) :
    let hseed := seed_eq E m b hthree
    E.V₃ = V ∧ E.U = E.W ∧
    Nonempty (ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) 2)) ∧
    Nonempty (ActionEquiv (pointAction E f hseed hK)
      (repeated (linearNatural E.input.field 2) 2)) ∧
    Nonempty (Outside.NaturalPair E) ∧
    Nat.card E.W = (2 ^ E.input.field.degree) ^ 5 ∧
    E.W = E.K.pCoreIn 2 ∧ E.W = E.L₁.pCoreIn 2 ∧ E.W ≤ L ∧
    E.W ⊓ centralizer (L : Set G) = ⊥ ∧ L.pCoreIn 2 = V ∧
    LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let hseed := seed_eq E m b hthree
  have hUW : E.U = E.W := by
    change conjugateSpanBy E.V₃ E.G₁ = conjugateSpanBy V E.G₁
    rw [hseed]
  have hcard := closure_card E f hK hseed d hUT hf hc hsum hspecial
  have hsplit := original_core_and_split E f hK hseed d hUT hf hc hsum
  have hfixed := closure_fixed_eq_bot E f hK hseed d hsum
  obtain ⟨r, ⟨e⟩⟩ := hsum
  have hr := multiplicity_eq_two E f hK hseed e hcard (point_card E m b d hpoint)
  subst r
  have hcores := original_residual_core_eq E f hseed hK e d hUT hf hc
  exact ⟨hseed, hUW, ⟨e⟩, ⟨pointMarking E f hseed hK e⟩,
    ⟨naturalPair E f hseed hK e⟩, hcard, hcores.1, hcores.2, hsplit.1,
    hfixed, hsplit.2.1, hsplit.2.2⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
