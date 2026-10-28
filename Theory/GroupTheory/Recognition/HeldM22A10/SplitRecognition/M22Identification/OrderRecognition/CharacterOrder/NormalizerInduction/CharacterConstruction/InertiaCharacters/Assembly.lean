module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Fusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.RootCentralizers
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Completion

/-!
# The induced block reduced to three actual centralizer orders

Internal fusion is supplied by the original actor conjugator, and the five
special centralizer orders by their root transporter property. Only the
centralizers of a, c and bd remain explicit. With their orders 32, 36 and 8,
character norm integrality fixes the order-four fusion, and all five induced
characters have the printed table values and norm one.

This is conditional assembly, not the existence theorem until those three
orders have been proved. The final unconditional assembly remains with the
normalizer inertia character construction.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Section 6, pp.10–11.
-/
open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L in
/-- Combine the three actor centralizers with the six already established orders. -/
public theorem normalizerFixedCentralizer_card_of_actors
    (hc : ∀ i : Fin 3, Nat.card (centralizer
      ({normalizerFixedRepresentative D k (Fin.natAdd 6 i)} :
        Set (normalizer (CaseII.E D k : Set G)))) = (![32, 36, 8] i : ℕ))
    (i : Fin 9) : Nat.card (centralizer ({normalizerFixedRepresentative D k i} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders i := by
  fin_cases i
  · exact normalizerFixedCentralizer_card_special D k L 0
  · exact normalizerFixedCentralizer_card_special D k L 1
  · exact normalizerFixedCentralizer_card_special D k L 2
  · exact normalizerFixedCentralizer_card_special D k L 3
  · exact normalizerFixedCentralizer_card_special D k L 4
  · exact normalizerFixedCentralizer_card_identity D k L
  · exact hc 0
  · exact hc 1
  · exact hc 2

include L in
/-- The three group-theoretic actor centralizer orders suffice for the actual induced block. -/
public theorem nonempty_normalizerInducedBlock_of_actor_centralizers
    (Q : NormalizerClassData D k)
    (hc : ∀ i : Fin 3, Nat.card (centralizer
      ({normalizerFixedRepresentative D k (Fin.natAdd 6 i)} :
        Set (normalizer (CaseII.E D k : Set G)))) = (![32, 36, 8] i : ℕ)) :
    Nonempty (NormalizerInducedBlock Q) := by
  obtain ⟨swap, hf⟩ := exists_normalizerInertiaFusion D k L
  exact nonempty_normalizerInducedBlock_of_fusion_centralizers D k L Q swap hf
    (normalizerFixedCentralizer_card_of_actors D k L hc)
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
