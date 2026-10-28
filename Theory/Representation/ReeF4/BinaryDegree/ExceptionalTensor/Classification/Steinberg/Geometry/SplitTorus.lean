module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights

/-!
# The F4 split torus and the actual positive coroot words

The rank-four torus is the closed image of the literal integral diagonal
matrices. Its negative coordinate cocharacters equal `n(t)n(1)⁻¹` in the
root-generated carrier. This comparison connects the algebraic torus to the
coroot convention used by the basic highest weights and the root-model
construction; it assumes neither a root model nor its torus identification.

Source: Steinberg, *Lectures on Chevalley Groups*, Lemmas 5–6, and GLS3,
Sections 1.12 and 1.14.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem algebraicNElement_ambient (r : F4Chevalley.Root) (t : Fˣ) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints (algebraicNElement r t) =
      F4Chevalley.matrixToAmbient (F4Chevalley.matrixN (F := F) r t) := by
  simp only [algebraicNElement, algebraicRootElement, map_mul,
    F4Chevalley.rootMorphism_inclusion_apply, F4Chevalley.matrixN,
    F4Chevalley.matrixToAmbient_root]

/-- The positive simple-coroot word is the inverse-parameter diagonal matrix. -/
theorem algebraicCorootElement_ambient (i : Fin 4) (t : Fˣ) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicCorootElement (typeF4SimpleRootIndex i) t) =
      F4Chevalley.matrixToAmbient (F4Chevalley.matrixH (F := F)
        (typeF4RootPairing_baseEquiv i) t) := by
  rw [algebraicCorootElement, map_mul, map_inv, algebraicNElement_ambient,
    algebraicNElement_ambient, ← map_inv, ← map_mul]
  congr 1
  rw [F4Chevalley.matrixH, F4Chevalley.matrixN_neg_one]
  rfl

/-- The concrete torus cocharacter is exactly the existing positive coroot. -/
theorem splitTorusSimpleCoroot_eq_algebraicCoroot (i : Fin 4)
    (t : Variety.Point (KMult F)) :
    letI := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
    (F4Chevalley.splitTorus (k := F)).inclusion.onPoints
      ((F4Chevalley.splitTorusSimpleCoroot (k := F) i).onPoints t) =
      algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0) := by
  let _ := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  rw [F4Chevalley.splitTorusSimpleCoroot_ambient_apply, algebraicCorootElement_ambient]

/-- Every positive simple-coroot value belongs to the concrete rank-four torus. -/
theorem algebraicCorootElement_mem_splitTorus (i : Fin 4) (t : Fˣ) :
    algebraicCorootElement (typeF4SimpleRootIndex i) t ∈ F4Chevalley.splitTorus (k := F) := by
  let _ := (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup
  let x : Variety.Point (KMult F) := (dPointEquiv 1).symm (fun _ => t)
  have hx : dPointEquiv 1 x 0 = t := by simp [x]
  rw [← hx, ← splitTorusSimpleCoroot_eq_algebraicCoroot]
  have h := Set.mem_range_self (f := (F4Chevalley.splitTorus (k := F)).inclusion.onPoints)
    ((F4Chevalley.splitTorusSimpleCoroot (k := F) i).onPoints x)
  rw [(F4Chevalley.splitTorus (k := F)).range_inclusion] at h
  exact h

/-- The maximal torus candidate contains all of the source simple-coroot values. -/
theorem algebraicCorootElement_mem_maximalTorus (i : Fin 4) (t : Fˣ) :
    algebraicCorootElement (typeF4SimpleRootIndex i) t ∈
      F4Chevalley.maximalTorus (k := F) :=
  F4Chevalley.splitTorus_le_maximalTorus (algebraicCorootElement_mem_splitTorus i t)

end ReeF4.BinaryDegree.ExceptionalTensor
