module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Assembly

/-!
# Normalizing the long–long exchange at q = 2

Replace the highest long-root section by the commutator of the first two
long roots at parameter one. Its image is the prescribed highest root.
The commuting-pair hypothesis makes this commutator commute with its first
entry, so the commutator identity for the square of that involutory entry
proves that the new highest lift is involutory. The literal fixed field has
two elements, and this gives its entire additive section and the long–long
exchange for every parameter. All short sections and the first two long
sections are retained.

This supplies one of the three upper relations in the final normalization.
The two short-pair trace relations and the lower exchanges remain separate
mathematical obligations. Source: GLS3 §2.4.5(b)(1), §6.1;
Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section

open Triality.Standard
open Triality.Standard.RadicalCoordinates.LeviCommutators
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
variable {E : Type*} [Group E] {f : E →* G}

private theorem long_square (L : RootSections 1 Nat.zero_lt_one f)
    (i : Fin 3) (s : fixedField P) : L.longRoot i (.ofAdd s) ^ 2 = 1 := by
  rw [← map_pow]
  have h : (Multiplicative.ofAdd s) ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change s + s = 0
    apply Subtype.ext
    exact CharTwo.add_self_eq_zero (s.val : GaloisField 2 3)
  rw [h, map_one]

private theorem inv_of_square {x : E} (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)

private theorem exchange_commutator {x y : E} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    x * y = y * x * ⁅x,y⁆ := by
  rw [commutatorElement_def, inv_of_square hx, inv_of_square hy]
  have hx' : x * x = 1 := by simpa only [pow_two] using hx
  have hy' : y * y = 1 := by simpa only [pow_two] using hy
  calc
    x * y = (y * (x*x) * y) * (x*y) := by rw [hx', mul_one, hy', one_mul]
    _ = _ := by group

/-- The highest lift specified by the long–long commutator, without choices. -/
def longPairHighest (L : RootSections 1 Nat.zero_lt_one f) : E :=
  ⁅L.longRoot 0 (.ofAdd 1), L.longRoot 1 (.ofAdd 1)⁆

/-- Its projection is the literal highest folded root. -/
theorem longPairHighest_project (L : RootSections 1 Nat.zero_lt_one f) :
    f (longPairHighest L) = long P rfl 2 1 := by
  have he := congrArg f (exchange_commutator (long_square L 0 1) (long_square L 1 1))
  simp only [map_mul, L.project_long] at he
  have hb := long_zero_one_exchange P rfl 1 1
  rw [mul_one] at hb
  exact mul_left_cancel (he.symm.trans hb)

/-- Exact commutation with the highest root removes the possible fourth-order defect. -/
theorem longPairHighest_square (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    longPairHighest L ^ 2 = 1 := by
  let x := L.longRoot 0 (.ofAdd 1)
  let y := L.longRoot 1 (.ofAdd 1)
  have hc0 : Commute x (L.longRoot 2 (.ofAdd 1)) := by
    have h := hcomm 1 5 (0, ![1,0,0]) (0, ![0,0,1]) (by decide) (by simp [interactingPair])
    simpa [RootSections.factor, x] using h
  have hc : Commute x ⁅x,y⁆ := by
    apply commutatorElement_eq_one_iff_commute.mp
    change ⁅x, longPairHighest L⁆ = 1
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl
      ((longPairHighest_project L).trans (L.project_long 2 1).symm)]
    exact hc0.commutator_eq
  have h := commutatorElement_mul_left_eq_conj_mul x x y
  rw [hc.eq, mul_inv_cancel_right, ← pow_two, long_square L 0 1,
    commutatorElement_one_left] at h
  exact (show ⁅x,y⁆ ^ 2 = 1 by simpa only [pow_two] using h.symm)

/-- Keep five sections and use the long commutator for the highest section. -/
def longPairSections (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    RootSections 1 Nat.zero_lt_one f where
  shortRoot := L.shortRoot
  longRoot i := if i = 2 then binaryRootLift (longPairHighest L)
      (longPairHighest_square hk L hcomm) else L.longRoot i
  project_short := L.project_short
  project_long i t := by
    split_ifs with hi
    · subst i
      rcases fixedField_cases t with rfl | rfl
      · rw [show Multiplicative.ofAdd (0 : fixedField P) = 1 from rfl, map_one, map_one]
        exact (long_zero P rfl 2).symm
      · simpa [binaryRootLift] using longPairHighest_project L
    · exact L.project_long i t

/-- Normalizing the long–long pair does not alter any short section. -/
theorem longPairSections_short (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    (longPairSections hk L hcomm).shortRoot = L.shortRoot := rfl

/-- The ten commuting pairs persist after the normalization. -/
theorem longPairSections_commutingPairs (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    CommutingPairs (longPairSections hk L hcomm) :=
  (commutingPairs_iff hk L _).mp hcomm

/-- The normalized sections satisfy the exact long–long exchange on both binary parameters. -/
theorem longPairSections_exchange (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L)
    (s t : fixedField P) :
    (longPairSections hk L hcomm).longRoot 0 (.ofAdd s) *
        (longPairSections hk L hcomm).longRoot 1 (.ofAdd t) =
      (longPairSections hk L hcomm).longRoot 1 (.ofAdd t) *
        (longPairSections hk L hcomm).longRoot 0 (.ofAdd s) *
        (longPairSections hk L hcomm).longRoot 2 (.ofAdd (s*t)) := by
  rcases fixedField_cases s with rfl | rfl <;>
    rcases fixedField_cases t with rfl | rfl
  all_goals simp only [longPairSections, ↓reduceIte, mul_zero, mul_one,
    show Multiplicative.ofAdd (0 : fixedField P) = 1 from rfl, map_one,
    one_mul]
  simpa [binaryRootLift, longPairHighest] using
    exchange_commutator (long_square L 0 1) (long_square L 1 1)

/-- The actual long–long relation discharges the `(1,4)` collector obligation. -/
theorem longPairSections_pairExchange (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    PairExchange (longPairSections hk L hcomm) 1 4 := by
  intro a b
  refine ⟨[(5, (0, ![0,0,a.2 0 * b.2 1]))], ?_, ?_⟩
  · simp [height]
  · simpa [RootSections.factor, FilteredCollection.wordProduct] using
      longPairSections_exchange hk L hcomm (a.2 0) (b.2 1)

/-- This normalization is an allowed additive central adjustment of the original system. -/
theorem exists_longPairAdjustment (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L) :
    ∃ A : CentralAdjustment f,
      A.adjusted hk L = longPairSections hk L hcomm ∧
      PairExchange (A.adjusted hk L) 1 4 := by
  refine ⟨adjustmentBetween hk L (longPairSections hk L hcomm),
    adjustmentBetween_adjusted hk L _, ?_⟩
  rw [adjustmentBetween_adjusted]
  exact longPairSections_pairExchange hk L hcomm

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
