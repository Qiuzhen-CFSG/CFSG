module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Lifting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Parameters
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.LinearThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Even
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Frattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Fitting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.NilpotentFixedCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.NilpotentFullNormalizer

/-!
# Component field detection: the common lifting step

The field-torus producer supplies a faithful coefficient torus in a literal
two-core quotient, with lifts in N_G(T) and the original Cartan action.
The lifting theorem constructs an odd subgroup and proves its movement
modulo T, giving exactly the shared component-detection contract.

The even-degree source consumer is complete in `Even`, using the constructed
Suzuki orbit and field actor. The odd-degree linear and unitary movement
constructions are complete. `Frattini` proves clause (4) for both parities:
ordinary quotient components lift to the quasisimple rows already excluded
by the sieve, and A.1.26 controls the Fitting subgroup independently.
`Fitting` puts every component commutator in the literal Fitting preimage,
both intrinsically and in Y. `NilpotentFixedCover` constructs a surjection
from the actual Cartan-fixed perfect residual to the remaining SL₂(5)
Fitting quotient, with solvable kernel. `NilpotentFullNormalizer` uses the
primary-plane trace to lift a cubic into I ∩ N_G(T), and excludes it for the
symplectic marking. This proves clauses (3--4) for that marking. The odd-degree
SL₃ nilpotent-Fitting branch remains open.
The common field-torus consumer
below remains useful for that branch; the preceding split-Cartan marking is
explicit in `Parameters`.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The exact shared output from constructed field-torus sections. The
component recognition and normalizer-lift premises remain with their producers. -/
theorem component_borel_detection_of_field_tori
    (hsections : ∀ I : Subgroup G, Source.ComponentIn E.Y I →
      ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2 → Nonempty (FieldTorusSection E)) :
    E.ComponentBorelDetection := by
  intro I hI hm
  obtain ⟨s⟩ := hsections I hI hm
  exact s.borel_movement

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
