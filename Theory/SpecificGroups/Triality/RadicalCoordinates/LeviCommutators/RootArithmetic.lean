module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.FoldedRoots

/-!
# Additive folded roots and generation of the arms highest root

The three roots in each short orbit commute, by the checked D₄ root-sum
table and the actual Geck non-sum relations. Their folded product is therefore
additive in its cubic-field parameter. The singleton roots are additive as
well. The checked exchange between positions 3 and 10 produces position 11;
hence any subgroup containing those first two singleton groups contains the
highest-root group. This supplies the torus-fixed factor of the arms radical.

Source: GLS3 2.4.5 and §2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics PositiveCoordinates PositiveCoordinates.SumExchangeData

private theorem short_positions_nonsum (i j k : Fin 3) :
    ∀ l : Fin 12, (shortPosition i j, shortPosition i k, l) ∉ sumTriples := by
  revert i j k
  decide +kernel

theorem shortSplit_curves_commute (P : Parameters) (i j k : Fin 3)
    (s t : ExtensionField P) :
    Commute (curve P (shortPosition i j) s) (curve P (shortPosition i k) t) := by
  by_cases he : shortPosition i j = shortPosition i k
  · rw [he]
    show curve P (shortPosition i k) s * curve P (shortPosition i k) t =
      curve P (shortPosition i k) t * curve P (shortPosition i k) s
    rw [← curve_add, ← curve_add, add_comm s t]
  · apply nonsumCommute_parameters P _ _ he
    rintro ⟨l, hl⟩
    exact short_positions_nonsum i j k l
      ((mem_sumTriples_iff _ _ l).mpr ((root_sum_iff _ _ l).mp hl))

theorem shortSplit_add (P : Parameters) (i : Fin 3) (s t : ExtensionField P) :
    shortSplit P i (s + t) = shortSplit P i s * shortSplit P i t := by
  simp only [shortSplit, map_add, curve_add]
  rw [(shortSplit_curves_commute P i 0 1 t (fieldFrobenius P s)).mul_mul_mul_comm]
  rw [((shortSplit_curves_commute P i 0 2 t
      (fieldFrobenius P (fieldFrobenius P s))).mul_left
    (shortSplit_curves_commute P i 1 2 (fieldFrobenius P t)
      (fieldFrobenius P (fieldFrobenius P s)))).mul_mul_mul_comm]

theorem short_add (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (s t : ExtensionField P) : short P hp i (s + t) = short P hp i s * short P hp i t := by
  simp only [short, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val]
  exact shortSplit_add P i s t

theorem long_add (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (s t : fixedField P) : long P hp i (s + t) = long P hp i s * long P hp i t := by
  simp only [long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, longElementary_val, longSplit, Subfield.coe_add, curve_add]

theorem long_zero_one_exchange (P : Parameters) (hp : P.prime = 2)
    (s t : fixedField P) :
    long P hp 0 s * long P hp 1 t =
      long P hp 1 t * long P hp 0 s * long P hp 2 (s * t) := by
  have hs : SumExchange P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  simp only [long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, longElementary_val, longSplit, longPosition,
    Matrix.cons_val_zero, Subfield.coe_mul]
  exact hs 3 10 11 ((root_sum_iff 3 10 11).mpr
    ((mem_sumTriples_iff 3 10 11).mp (by decide))) s.val t.val

/-- Internal root multiplication supplies the torus-fixed highest root. -/
theorem long_two_mem_of_zero_one (P : Parameters) (hp : P.prime = 2)
    (H : Subgroup (Carrier P)) (h0 : ∀ t, long P hp 0 t ∈ H)
    (h1 : ∀ t, long P hp 1 t ∈ H) (t : fixedField P) : long P hp 2 t ∈ H := by
  have he := long_zero_one_exchange P hp t 1
  rw [mul_one] at he
  have hm := H.mul_mem (H.inv_mem (H.mul_mem (h1 1) (h0 t)))
    (H.mul_mem (h0 t) (h1 1))
  rw [he, inv_mul_cancel_left] at hm
  exact hm

end Triality.Standard.RadicalCoordinates.LeviCommutators
