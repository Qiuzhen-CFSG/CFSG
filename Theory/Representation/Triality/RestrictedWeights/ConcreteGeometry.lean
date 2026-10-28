module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceSimplicity
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.GraphField
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry

/-!
# Concrete graph-field geometry for restricted triality modules

This assembles the actual Clifford Spin pinning, character lattice, opposite
Borels, graph map and Frobenius map. The only remaining geometric input is
universality of this algebraic group. No representation or classification
conclusion is an input. It supplies the literal geometry used by restricted
highest-weight and Steinberg tensor constructions.

Source: GLS3, §§1.14 and 2.8; Steinberg, §§12–13.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def simpleRootEquiv : Fin 4 ≃ {a : (pinnedRootData k).Root // a ∈ (pinnedRootData k).simple} :=
  Equiv.ofBijective (fun i => ⟨pinnedRootIndex k (simpleRoot i),by
    rw [pinnedRootData_simple]
    exact ⟨i,rfl⟩⟩) (by
      constructor
      · intro i j h
        exact typeDSimpleRootIndex_injective 2 (congrArg (fun a => a.val.down) h)
      · rintro ⟨a,ha⟩
        rw [pinnedRootData_simple] at ha
        obtain ⟨i,rfl⟩ := ha
        exact ⟨i,rfl⟩)

def weightEquiv : Multiplicative (Fin 4 → ℤ) ≃* TorusWeight (CorootTorus.closedSubgroup k) :=
  (AddEquiv.toMultiplicative (characterLatticeEquiv k)).trans (MulEquiv.multiplicativeAdditive _)

theorem weightEquiv_apply (a : Fin 4 → ℤ) :
    weightEquiv k (Multiplicative.ofAdd a) = CorootTorus.weightEmbedding k a :=
  characterLatticeEquiv_apply k a

theorem weight_coordinate (a : Fin 4 → ℤ) (i : Fin 4) :
    (pinnedRootData k).weightPairing (weightEquiv k (Multiplicative.ofAdd a))
      (simpleRootEquiv k i).val = a i := by
  apply (weightCocharacterEquation_existsUnique (CorootTorus.closedSubgroup k)
    (weightEquiv k (Multiplicative.ofAdd a))
    ((pinnedRootData k).rootCocharacter (simpleRootEquiv k i).val)).unique
  · exact (pinnedRootData_isRealization k).weightPairing_spec _ _
  · rw [weightEquiv_apply]
    exact pinnedRootData_weight_simpleCoroot k a i

def finiteGeometry (hu : IsUniversalVersion (groupVariety k)) :
    FiniteRestriction.Geometry (groupVariety k) where
  simple := source_simple k
  universal := hu
  torus := CorootTorus.closedSubgroup k
  maximalTorus := CorootTorus.isMaximal k
  roots := pinnedRootData k
  realized := pinnedRootData_isRealization k
  additionComplete := pinnedRootData_isRootAdditionComplete k
  rootIndex := Equiv.ulift
  based := pinnedRootData_isActualBasedRootPairing k
  positive := fun _ => Iff.rfl
  simpleRoot := simpleRootEquiv k
  simpleRoot_index := fun _ => rfl
  bigCell := OppositeBorels.bigCell k
  weight := weightEquiv k
  weight_coordinate := weight_coordinate k
  rootParameter := pinnedRootParametrization k
  diagram := Diagram.pinnedIso k
  diagram_three := Diagram.pinnedAut_cube k
  diagram_root := by
    intro a t
    simp only [pinnedRootParametrization_inclusion]
    change Diagram.pinnedAut k (rootPoint k a.down t) =
      rootPoint k (typeD4DiagramEquiv.indexEquiv a.down) t
    exact GraphField.diagram_rootPoint k a.down t
  frobenius := regularFrobeniusLift k 1
  frobenius_bijective := regularFrobeniusLift_bijective k 1
  frobenius_root := by
    intro a t
    simp only [pinnedRootParametrization_inclusion, regularFrobeniusLift_onPoints]
    exact GraphField.frobenius_rootPoint k 1 a.down t
  commute := by
    intro g
    simpa only [regularFrobeniusLift_onPoints, Diagram.pinnedAut] using GraphField.frobenius_diagram_commute k 1 g
  fixed_finite := GraphField.orientation_fixed_finite k

end Triality.RestrictedWeights.Concrete
