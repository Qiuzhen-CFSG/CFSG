module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.ClassSums

/-!
# Normalizer centralizers of the five special representatives

The special-set transporter theorem puts each ambient centralizer inside N(E).
Restriction to N(E) therefore preserves its order, giving the five root columns.
The identity column follows from the already proved order of N(E).

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Lemma 10 and the Section 6 normalizer table.
-/
open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L in
private theorem special_centralizer (r : Fin 5) :
    Nat.card (centralizer ({normalizerRepresentative D k r} :
      Set (normalizer (CaseII.E D k : Set G)))) = (![384, 12, 8, 32, 16] r : ℕ) := by
  let a := normalizerRepresentative D k r
  have ha : a ∈ normalizerSpecialSupport D k := ⟨r, IsConj.refl _⟩
  have hle : centralizer ({(a : G)} : Set G) ≤ normalizer (CaseII.E D k : Set G) := by
    intro g hg
    apply normalizerSpecialSupport_transporters D k a a ha ha g
    have he := mem_centralizer_singleton_iff.mp hg
    calc
      g⁻¹ * (a : G) * g = g⁻¹ * ((a : G) * g) := by rw [mul_assoc]
      _ = (a : G) := by rw [← he, inv_mul_cancel_left]
  have hs : centralizer ({a} : Set (normalizer (CaseII.E D k : Set G))) =
      (centralizer ({(a : G)} : Set G)).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf]
    exact Subtype.ext_iff
  change Nat.card (centralizer ({a} : Set (normalizer (CaseII.E D k : Set G)))) = _
  rw [hs, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  change Nat.card (centralizer ({CaseII.into D k (specialRepresentative r)} : Set G)) = _
  fin_cases r
  · change Nat.card (centralizer ({CaseII.into D k (CaseII.z 0)} : Set G)) = 384
    rw [CaseII.into_z_zero]
    exact D.centralizer_card
  · exact L.centralizer_orders 3
  · exact L.centralizer_orders 2
  · exact L.centralizer_orders 0
  · exact L.centralizer_orders 1

include L in
/-- The five root columns have the source centralizer orders inside the actual normalizer. -/
public theorem normalizerFixedCentralizer_card_special (r : Fin 5) :
    Nat.card (centralizer ({normalizerFixedRepresentative D k (Fin.castAdd 4 r)} :
      Set (normalizer (CaseII.E D k : Set G)))) =
      normalizerFixedCentralizerOrders (Fin.castAdd 4 r) := by
  have he : normalizerFixedRepresentative D k (Fin.castAdd 4 r) = normalizerRepresentative D k r := by
    fin_cases r <;> rfl
  rw [he, special_centralizer D k L]
  fin_cases r <;> rfl

include L in
omit [Finite G] in
/-- The identity column centralizer is the full normalizer of order 5760. -/
public theorem normalizerFixedCentralizer_card_identity :
    Nat.card (centralizer ({normalizerFixedRepresentative D k 5} :
      Set (normalizer (CaseII.E D k : Set G)))) = normalizerFixedCentralizerOrders 5 := by
  have he : normalizerFixedRepresentative D k 5 = 1 := (normalizerCentralizer D k).map_one
  rw [he, show centralizer ({(1 : normalizer (CaseII.E D k : Set G))} : Set _) = ⊤ from by
    ext x
    simp [mem_centralizer_singleton_iff]]
  rw [Subgroup.card_top]
  exact normalizer_E_card D k L
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
