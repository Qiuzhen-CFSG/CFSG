module

public import Theory.Representation.G2NaturalBinary
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.Representation.BinaryOffender.EquivariantStabilizer

/-!
# The literal marked plane in the binary natural G₂ module

The plane is the span of the classes of the second and first null octonion
basis vectors, in that order. This module fixes the common interface for its
Sylow invariance and stabilizer calculations. All actors belong to the actual
commutator subgroup and all coefficient maps act on the trace-zero quotient.

Source: Aschbacher–Smith, printed p.1132 (PDF p.1149), C.1.30 and B.5.3–6.
The octonion conventions are inherited from the attributed ATLAS port;
see LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.BinaryPlane
open Representation.BinaryOffender

abbrev Actor := commutator (Atlas.G2.Model (ZMod 2))
abbrev Coefficients := Atlas.G2.Natural.Space (ZMod 2)
abbrev action := Atlas.G2.Natural.derivedAction (ZMod 2)

/-- The second null octonion basis vector, with its actual trace-zero proof. -/
def firstRepresentative : TraceZero (ZMod 2) :=
  ⟨![0,1,0,0,0,0,0,0], by change Atlas.SplitOctonion.trace _ = 0; decide +kernel⟩

/-- The first null octonion basis vector. -/
def secondRepresentative : TraceZero (ZMod 2) :=
  ⟨![1,0,0,0,0,0,0,0], by change Atlas.SplitOctonion.trace _ = 0; decide +kernel⟩

def firstVector : Coefficients := mk (ZMod 2) firstRepresentative
def secondVector : Coefficients := mk (ZMod 2) secondRepresentative

/-- The specified plane in the original natural quotient. -/
def standardPlane : Submodule (ZMod 2) Coefficients :=
  Submodule.span (ZMod 2) {firstVector, secondVector}

@[simp] theorem coordinates_firstVector :
    binaryCoordinates (ZMod 2) firstVector = ![0,1,0,0,0,0] := rfl

@[simp] theorem coordinates_secondVector :
    binaryCoordinates (ZMod 2) secondVector = ![1,0,0,0,0,0] := rfl

/-- Membership in the marked plane uses precisely its four vanishing coordinates. -/
theorem mem_standardPlane_iff (v : Coefficients) :
    v ∈ standardPlane ↔
      binaryCoordinates (ZMod 2) v 2 = 0 ∧ binaryCoordinates (ZMod 2) v 3 = 0 ∧
      binaryCoordinates (ZMod 2) v 4 = 0 ∧ binaryCoordinates (ZMod 2) v 5 = 0 := by
  change v ∈ Submodule.span (ZMod 2) {firstVector, secondVector} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a,b,rfl⟩
    simp
  · intro h
    refine ⟨binaryCoordinates (ZMod 2) v 1, binaryCoordinates (ZMod 2) v 0,
      binaryCoordinates_injective _ ?_⟩
    rw [map_add, map_smul, map_smul, coordinates_firstVector, coordinates_secondVector]
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The two surviving coordinates are a genuine parametrization of the plane. -/
def standardPlaneEquiv : standardPlane ≃ (ZMod 2 × ZMod 2) where
  toFun v := (binaryCoordinates (ZMod 2) v.val 0, binaryCoordinates (ZMod 2) v.val 1)
  invFun p := ⟨p.2 • firstVector + p.1 • secondVector,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))⟩
  left_inv v := by
    apply Subtype.ext
    apply binaryCoordinates_injective (ZMod 2)
    have h := (mem_standardPlane_iff v.val).mp v.property
    simp only [map_add, map_smul, coordinates_firstVector, coordinates_secondVector]
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  right_inv p := by simp

/-- The literal marked plane has order four. -/
theorem card_standardPlane : Nat.card standardPlane = 4 := by
  rw [Nat.card_congr standardPlaneEquiv]
  simp

/-- The standard Sylow subgroup, restricted to the actual derived group. -/
abbrev standardSylow : Sylow 2 Actor := BinaryParabolicPair.derivedSylow

/-- The natural linear change of coordinates attached to an inner automorphism. -/
def innerCoordinates (g : Actor) : Coefficients ≃ₗ[ZMod 2] Coefficients :=
  LinearEquiv.ofBijective (action g) (action.apply_bijective g)

@[simp] theorem innerCoordinates_apply (g : Actor) (v : Coefficients) :
    innerCoordinates g v = action g v := rfl

/-- The group conjugation and the natural linear action are compatible. -/
theorem innerCoordinates_equivariant (g a : Actor) (v : Coefficients) :
    innerCoordinates g (action a v) = action (MulAut.conj g a) (innerCoordinates g v) := by
  change action g (action a v) = action (g * a * g⁻¹) (action g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  simp only [inv_mul_cancel_right]

/-- The previously established order of the actual derived group. -/
theorem card_actor : Nat.card Actor = 6048 := by
  rw [Actor, BinaryParabolicPair.commutator_eq_longRootClosure]
  exact BinaryException.card_H

/-- The standard Sylow subgroup has the full 2-part of the group order. -/
theorem card_standardSylow : Nat.card standardSylow = 32 :=
  BinaryParabolicPair.card_derivedSylow

end Atlas.G2.Natural.BinaryPlane
