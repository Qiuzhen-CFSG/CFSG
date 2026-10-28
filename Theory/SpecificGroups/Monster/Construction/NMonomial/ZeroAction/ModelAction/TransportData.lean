module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural.Coordinates

/-!
# Geometric inputs for cyclic tensor transport

The source construction uses the permutation of the three Parker axes, the
actual coordinate halfspaces, and conjugation of the specified orbit and sign
involutions. This interface separates those group facts from linear transport.
It contains no representation or extension premise. Constructing a witness is
an outstanding group-theoretic obligation; the record itself proves no clause
of the source theorem.

Source: Aschbacher, *Sporadic Groups*, Sections 14 and 27 and formula 29.7.5,
printed pp. 156–157. Conjugation uses left composition.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction
open TrialitySpin SignedModules

/-- The three actual orbit involutions, with zero-based source indices. -/
def axisK : Natural.Axis → N
  | 0 => k1
  | 1 => k2
  | 2 => k3

/-- The three actual central sign involutions, in the same indexing. -/
def axisZ : Natural.Axis → N
  | 0 => z1N
  | 1 => z2N
  | 2 => z3N

/-- Earlier-source geometric data needed to transport the six oriented tensor spaces.
No witness is assumed by the full model-action task. -/
structure AxisTransportData where
  permutation : N →* Equiv.Perm Natural.Axis
  halfspaces : ∀ (g : N) (i : Natural.Axis),
    Natural.Carries i (permutation g i) g.val
  conjugate_k : ∀ (g : N) (i : Natural.Axis),
    g * axisK i * g⁻¹ = axisK (permutation g i)
  conjugate_z : ∀ (g : N) (i : Natural.Axis),
    g * axisZ i * g⁻¹ = axisZ (permutation g i)

/-- Halfspace transport also supplies the actual action on each whole Parker axis. -/
theorem AxisTransportData.image_axis (H : AxisTransportData) (g : N) (i : Natural.Axis) :
    g.val '' Set.range (Natural.point i) = Set.range (Natural.point (H.permutation g i)) :=
  Natural.image_axis g.val (H.halfspaces g i)

end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction
