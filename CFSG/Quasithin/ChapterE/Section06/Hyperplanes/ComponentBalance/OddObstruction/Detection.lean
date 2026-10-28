module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Quotient
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models

/-!
# The outstanding component detection in E.6.19

The extraction output retains the actual component image in
C_G(A)/(O(C_G(A)) A), both displayed commutator equalities, and an ordinary
component of C_G(A) lifting it. The obstruction centralizer is inside the
actual induced automorphism group Aut_{C_G(A)}(L). It is not a centralizer
in an unrelated abstract automorphism group.

These definitions specify the remaining extraction and model-inspection
obligations. They assert neither Aschbacher's results nor E.6.19. The
quotient preparation is proved in `Quotient`; the final source assembly
belongs to the parent `OddObstruction` module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263), citing Aschbacher, *Finite Group Theory* (1986),
31.14(1) and 31.18. The subsequent inspection uses all five alternatives
of E.6.8, printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction

variable {G : Type*} [Group G]

/-- C_{Aut_{C_G(A)}(L)}(Aut_U(L)), formed with the existing conjugation images.
For the source inputs U ≤ C_G(A), `inducedAction_le` verifies that subgroupOf
retains all of Aut_U(L). -/
def actionCentralizer (A U L : Subgroup G) :
    Subgroup (inducedAutomizer L (centralizer (A : Set G))) :=
  centralizer ((inducedAutomizer L U).subgroupOf
    (inducedAutomizer L (centralizer (A : Set G))) :
      Set (inducedAutomizer L (centralizer (A : Set G))))

/-- The induced action inclusion uses the actual inclusions of the actors. -/
theorem inducedAction_le {A U L : Subgroup G} (hUH : U ≤ centralizer (A : Set G)) :
    inducedAutomizer L U ≤ inducedAutomizer L (centralizer (A : Set G)) :=
  map_mono (comap_mono hUH)

/-- The precise output still to be constructed by extraction and lifting.
Every subgroup and commutator is in its indicated relative ambient group. -/
structure DetectedComponent (A U V L : Subgroup G) : Prop where
  component : CentralizerComponent A L
  quotient_component : IsComponent (CentralizerQuotient A) (quotientImage A L)
  commutator_subspace : ⁅quotientImage A L, quotientImage A U⁆ = quotientImage A L
  commutator_oddCore :
    ⁅quotientImage A L, oddCentralizer (quotientImage A U)⁆ = quotientImage A L
  normalized : V ≤ normalizer (L : Set G)
  action_oddCore : pPrimeCore 2 (actionCentralizer A U L) ≠ ⊥

/-- The full earlier E.6.8 output, with its actual Q and every source clause.
It is permitted as an earlier-source input; no proof of it is supplied here. -/
def EarlierComponentAlternatives (M V Q : Subgroup G) : Prop :=
  ∀ A ∈ obstructionFamily M V, ∀ L : Subgroup G, CentralizerComponent A L →
    ¬ L ≤ M ∧ Components.ComponentAlternatives M V A Q L

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
