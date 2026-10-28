module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadRealization
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadFixedTransport

/-!
# The source elementary hexad subgroup

The checked standard translation module is the fixed space of the whole
native hexad two-core. Its six-dimensional singular coordinates transport
to every hexad and then through the literal Q/Z(Q) marking. Thus the exact
source E₁ is elementary of order 128, and its product with the cubic-central
rank-five factor is elementary of order 2048 and normalized by G₁,₃.

This discharges the native fixed-space premises in the construction of E.
It does not assert E = J(T) or identify its full ambient normalizer.
Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), proof of (4.6), p.598, DOI 10.1007/BF01232280.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry M22TripleCover

/-- The actual whole-two-core fixed space at every native design hexad. -/
theorem nativeHexadFixedSpace_data {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (nativeHexadFixedSpace B)=64 ∧
      ∀ v ∈ nativeHexadFixedSpace B, Unitary.quadraticForm v=0 :=
  nativeHexadFixedSpace_data_of_standard NativeHexadRealization.standard_card
    NativeHexadRealization.standard_singular hB

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The literal source E₁, with both elementary structure and exact order proved. -/
theorem originalHexadFixedCore_data {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) ∧
      Nat.card (originalHexadFixedCore h e X B)=128 := by
  let := h.extraspecial
  exact originalHexadFixedCore_data_of_native h e X
    (fun _ hb => nativeHexadFixedSpace_data hb) hB

/-- Constructed elementary E of order 2048, normalized by the whole source
hexad subgroup, and with its exact intersection with the original Q. -/
theorem originalHexadElementary_data {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (originalHexadFixedCore h e X B) ∧
    Nat.card (originalHexadFixedCore h e X B)=128 ∧
    IsElementaryAbelian 2 (originalHexadElementary h e X B) ∧
    Nat.card (originalHexadElementary h e X B)=2048 ∧
    originalPlaneHexad e B ≤ normalizer (originalHexadElementary h e X B : Set (centralizer z)) ∧
    originalHexadElementary h e X B ⊓ core z = originalHexadFixedCore h e X B :=
  originalHexadElementary_data_of_standard h e X NativeHexadRealization.standard_card
    NativeHexadRealization.standard_singular hB

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
