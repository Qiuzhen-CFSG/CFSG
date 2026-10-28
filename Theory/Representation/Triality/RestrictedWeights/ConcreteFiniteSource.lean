module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteFiniteClassification
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceUniversality

/-!
# Finite triality classification from the shared center theorem

The actual incoming-isogeny construction discharges algebraic universality.
This is its literal restricted-module consumer on the same Clifford Spin
carrier, retaining only the independent semisimple-center source theorem.
Source: GLS3 1.9.5(h), 1.12.5(b), and 2.8.2.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

theorem finiteRestrictedClassification_of_semisimple_centers
    (hcenter : ∀ (H : Variety k) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
      ∀ T : ClosedSubgroup H, IsMaximalTorus T →
        Subgroup.center (Variety.Point H) ≤ T.toSubgroup) (n : ℕ) (hn : 0<n) :
    let S := finiteGeometry k (source_universal_of_semisimple_centers k hcenter)
    LeftRestrictedIrreducibility S n ∧ LeftRestrictedSeparation S n ∧
      LeftRestrictedExhaustivity S n :=
  finiteRestrictedClassification k (source_universal_of_semisimple_centers k hcenter) n hn

end Triality.RestrictedWeights.Concrete
