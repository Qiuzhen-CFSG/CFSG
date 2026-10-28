module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers.FourGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Counting

/-!
# The relative centralizer of the literal max4 plane

Four ordered-basis words fix the two plane generators and send the third
basis vector of the eight to its four possible complements. Their translates
of the eight centralizer are disjoint and lie in the relative plane centralizer.
The existing eight-centralizer lower bound therefore yields 15728640 elements.
Matching a full ambient upper bound then forces containment in max4.

All actions concern the literal ATLAS max4 words, with the original numbering
and right-conjugation convention. Source context: Aschbacher--Smith A.3.12,
pp.47--48; Kleidman--Wilson (1988), pp.484--510.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.SymmetricLinear.NormalEight
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Max4EightAction
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

namespace PlaneCentralizer

abbrev relativeEightCentralizer : Subgroup max4Subgroup :=
  (centralizer (max4Eight : Set Model)).subgroupOf max4Subgroup

abbrev relativePlaneCentralizer : Subgroup max4Subgroup :=
  (centralizer (max4Plane : Set Model)).subgroupOf max4Subgroup

private theorem plane_le_eight : max4Plane ≤ max4Eight := by
  apply map_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨planeIndex i, rfl⟩

private theorem eightCentralizer_le_planeCentralizer :
    relativeEightCentralizer ≤ relativePlaneCentralizer := by
  intro g hg u hu
  exact hg u (plane_le_eight hu)

private theorem eightElement_mem (i : Fin 8) : (element i : Model) ∈ max4Eight :=
  mem_map_of_mem _ (show element i ∈ eight from ⟨i, rfl⟩)

private def word : List Bool → max4Subgroup
  | [] => 1
  | b :: w => (if b then y else x) * word w

private theorem word_conj (w : List Bool) (i : Fin 8) :
    (word w)⁻¹ * element i * word w = element (wordAction w i) := by
  induction w generalizing i with
  | nil => simp [word, wordAction]
  | cons b w ih =>
    cases b <;> simp only [word, wordAction, Bool.false_eq_true, if_false,
      if_true, mul_inv_rev]
    · calc
        _ = (word w)⁻¹ * (x⁻¹ * element i * x) * word w := by group
        _ = _ := by rw [element_conj_x, ih]
    · calc
        _ = (word w)⁻¹ * (y⁻¹ * element i * y) * word w := by group
        _ = _ := by rw [element_conj_y, ih]

private def complementIndex (i : Fin 4) : Fin 8 := ![3, 4, 6, 7] i

private theorem complementIndex_injective : Function.Injective complementIndex := by
  decide +kernel

private theorem complement_basis (i : Fin 4) : IsBasis 1 2 (complementIndex i) := by
  revert i
  decide +kernel

private def representative (i : Fin 4) : max4Subgroup :=
  (word (wordFor 1 2 (complementIndex i)))⁻¹

private theorem representative_conj (i : Fin 4) :
    (MulAut.conj (representative i)) (element 1) = element 1 ∧
    (MulAut.conj (representative i)) (element 2) = element 2 ∧
    (MulAut.conj (representative i)) (element 3) = element (complementIndex i) := by
  obtain ⟨h1, h2, h3⟩ := wordFor_spec 1 2 (complementIndex i) (complement_basis i)
  have hc (j : Fin 8) :
      (MulAut.conj (representative i)) (element j) =
        element (wordAction (wordFor 1 2 (complementIndex i)) j) := by
    simpa only [MulAut.conj_apply, representative, inv_inv] using
      word_conj (wordFor 1 2 (complementIndex i)) j
  exact ⟨(hc 1).trans (congrArg element h1), (hc 2).trans (congrArg element h2),
    (hc 3).trans (congrArg element h3)⟩

private theorem representative_fixes_plane (i j : Fin 4) :
    (MulAut.conj (representative i)) (element (planeIndex j)) =
      element (planeIndex j) := by
  fin_cases j
  · change (MulAut.conj (representative i)) (element 0) = element 0
    rw [element_zero, map_one]
  · exact (representative_conj i).1
  · exact (representative_conj i).2.1
  · change (MulAut.conj (representative i)) (element 5) = element 5
    have h : element 5 = element 1 * element 2 := (element_mul 1 2).symm
    rw [h, map_mul, (representative_conj i).1, (representative_conj i).2.1]

private theorem representative_mem (i : Fin 4) : representative i ∈ relativePlaneCentralizer := by
  rintro _ ⟨z, ⟨j, rfl⟩, rfl⟩
  have h := representative_fixes_plane i j
  have he : element (planeIndex j) * representative i = representative i * element (planeIndex j) := by
    have h' := congrArg (fun z => z * representative i) h
    simpa only [MulAut.conj_apply, inv_mul_cancel_right] using h'.symm
  exact congrArg (fun z : max4Subgroup => (z : Model)) he

private def translate : Fin 4 × relativeEightCentralizer → relativePlaneCentralizer := fun z =>
  ⟨representative z.1 * z.2, mul_mem (representative_mem z.1)
    (eightCentralizer_le_planeCentralizer z.2.property)⟩

private theorem translate_conj (i : Fin 4) (c : relativeEightCentralizer) :
    (MulAut.conj ((translate (i, c) : relativePlaneCentralizer) : max4Subgroup))
      (element 3) = element (complementIndex i) := by
  have hc : element 3 * (c : max4Subgroup) = c * element 3 := by
    apply Subtype.ext
    exact c.property _ (eightElement_mem 3)
  have hf : (MulAut.conj (c : max4Subgroup)) (element 3) = element 3 := by
    simp only [MulAut.conj_apply, ← hc, mul_inv_cancel_right]
  change (MulAut.conj (representative i * (c : max4Subgroup))) (element 3) = _
  rw [map_mul]
  change (MulAut.conj (representative i)) ((MulAut.conj (c : max4Subgroup)) (element 3)) = _
  rw [hf]
  exact (representative_conj i).2.2

private theorem translate_injective : Function.Injective translate := by
  rintro ⟨i, c⟩ ⟨j, d⟩ hij
  have he : i = j := complementIndex_injective (element_injective (by
    have hh := congrArg (fun z : relativePlaneCentralizer =>
      (MulAut.conj (z : max4Subgroup)) (element 3)) hij
    simpa only [translate_conj] using hh))
  subst j
  have hcd : c = d := Subtype.ext (mul_left_cancel
    (congrArg (fun z : relativePlaneCentralizer => (z : max4Subgroup)) hij))
  subst d
  rfl

/-- The four certified actions fixing the plane provide four disjoint translates
of the eight centralizer, all inside the actual relative plane centralizer. -/
theorem relative_centralizer_card_ge : 15728640 ≤ Nat.card relativePlaneCentralizer := by
  have hc := Nat.card_le_card_of_injective translate translate_injective
  rw [Nat.card_prod, Nat.card_fin] at hc
  have he := Max4EightCentralizer.relative_centralizer_card_ge
  change 3932160 ≤ Nat.card relativeEightCentralizer at he
  omega

/-- Matching the full ambient bound against the relative lower bound forces
containment in the literal max4 subgroup. -/
theorem centralizer_le_of_card_le
    (hc : Nat.card (centralizer (max4Plane : Set Model)) ≤ 15728640) :
    centralizer (max4Plane : Set Model) ≤ max4Subgroup := by
  have hl : 15728640 ≤ Nat.card (centralizer (max4Plane : Set Model) ⊓ max4Subgroup : Subgroup Model) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective Subtype.val_injective]
    exact relative_centralizer_card_ge
  have he := eq_of_le_of_card_ge (H := centralizer (max4Plane : Set Model) ⊓ max4Subgroup)
    (K := centralizer (max4Plane : Set Model)) inf_le_left (hc.trans hl)
  rw [← he]
  exact inf_le_right

end PlaneCentralizer
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
