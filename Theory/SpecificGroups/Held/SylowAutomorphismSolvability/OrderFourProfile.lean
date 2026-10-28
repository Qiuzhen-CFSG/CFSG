module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Checks
public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.Quotient
public import Theory.GroupTheory.PGroup.InvariantFiberAutomorphisms

/-!
# The intrinsic Held order-four profile

Transport the certified flags through the bijective original normal form and
the actual Frattini coordinate map. This gives the complete count of elements
whose fourth power is one and whose square is nontrivial in every coordinate
fiber: `[16,64,48,32,32,64,48,64,48,48,48,64,64,64,64,0]`.
These are precisely the elements of order four. The finite certificates are
shared by all fibers; none of the large permutation tests is repeated here.

Source: the literal ATLAS Held carrier and PC words, connected to the actual
Frattini graph quotient in `FrattiniCoordinates`. This intrinsic invariant
supplies the small quotient stabilizer argument in `Quotient`.
-/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile
open FrattiniCoordinates
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private theorem list_filter_card (p : Fin 1024 → Bool) :
    (Finset.univ.filter (fun n => p n = true)).card =
      ((List.finRange 1024).filter p).length := by
  rw [← List.toFinset_finRange 1024, ← List.toFinset_filter,
    List.toFinset_card_of_nodup ((List.nodup_finRange 1024).filter p)]

public theorem orderFour_fiber_card (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) (v : Coordinate) :
    f.predicateFiberCard (fun x => x ^ 4 = 1 ∧ x ^ 2 ≠ 1) v =
      countTable (vectorCode v) := by
  let e : Fin 1024 ≃ Representative := Equiv.ofBijective normalForm normalForm_bijective
  have hcard : Nat.card {x : Representative // f x = v ∧ (x ^ 4 = 1 ∧ x ^ 2 ≠ 1)} =
      Nat.card {n : Fin 1024 // indexCode n = vectorCode v ∧ orderFourTable n = true} := by
    apply (Nat.card_congr (e.subtypeEquiv ?_)).symm
    intro n
    change (_ ∧ _) ↔ (f (normalForm n) = v ∧ _)
    rw [normalForm_coordinate_eq_iff f hf, ← orderFourTable_correct, hasOrderFour_iff]
    rfl
  rw [MonoidHom.predicateFiberCard, hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hc := list_filter_card (fun n => indexCode n == vectorCode v && orderFourTable n)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rw [hc]
  have hv : vectorCode v < 16 := by
    have h : ∀ v : Coordinate, vectorCode v < 16 := by decide +kernel
    exact h v
  exact countTable_correct ⟨vectorCode v, hv⟩
end Held.SylowAutomorphismSolvability.OrderFourProfile
