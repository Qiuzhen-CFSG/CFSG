module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Coordinates

/-!
# The compatible quaternion-swap embedding and movement equations

The wreath map has exactly the diagonal central kernel. It therefore gives an
injective map of the literal quotient, carrying the marked plane to the fixed
natural four. The extra involution satisfies the prescribed twist, and the
inverse of the coordinate actor has all four required actions. Whole-overlap
coverage and generation of the second parabolic are established separately.
Source: Aschbacher--Smith, 14.2.21, printed p.988.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem rawValue_mul (w u : Raw) : rawValue (w * u) = rawValue w * rawValue u := by
  have hr : ∀ r : C2, r = 1 ∨ r = turn := by decide +kernel
  have htt : turn * turn = 1 := by decide +kernel
  have hti : turn⁻¹ = turn := by decide +kernel
  have ht : turn ≠ 1 := by decide +kernel
  have reorder (a b c d : QuaternionGroup 2) :
      leftMap a * leftMap b * (rightMap c * rightMap d) =
        leftMap a * rightMap c * (leftMap b * rightMap d) := by
    rw [mul_assoc, ← mul_assoc (leftMap b), left_right_commute b c]
    group
  have hs (q r : QuaternionGroup 2) :
      swap * (leftMap q * rightMap r) = (leftMap r * rightMap q) * swap := by
    rw [← mul_assoc, swap_left, mul_assoc, swap_right, ← mul_assoc,
      ← left_right_commute]
  rcases hr w.right with hw | hw <;> rcases hr u.right with hu | hu <;>
    simp only [rawValue, RegularWreathProduct.mul_left, RegularWreathProduct.mul_right,
      hw, hu, Pi.mul_apply, inv_one, one_mul, mul_one, hti, htt, ht, ↓reduceIte, map_mul]
  · exact reorder _ _ _ _
  · rw [reorder]; group
  · rw [reorder, mul_assoc _ swap, hs]
    group
  · rw [reorder, mul_assoc _ swap, ← mul_assoc swap, hs,
      mul_assoc _ swap swap, swap_square, mul_one]

def rawMap : Raw →* Carrier where
  toFun := rawValue
  map_one' := by decide +kernel
  map_mul' := rawValue_mul


theorem rawMap_ker : rawMap.ker = diagonalCenter := by
  ext w
  change rawValue w = 1 ↔ w = 1 ∨ w = killed
  have h : ∀ w : Raw, rawValue w = 1 ↔ w = 1 ∨ w = killed := by decide +kernel
  exact h w

/-- The literal embedding of the re-marked quaternion-swap model. -/
def movement : QH →* Carrier :=
  QuotientGroup.lift diagonalCenter rawMap rawMap_ker.ge

theorem movement_injective : Function.Injective movement :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr rawMap_ker.symm

theorem movement_projection (w : Raw) : movement (projection w) = rawMap w := rfl

theorem movement_left (q : QuaternionGroup 2) : movement (leftEmbedding q) = leftMap q := by
  change rawValue (leftRaw q) = leftMap q
  simp [rawValue, leftRaw, turn]

theorem movement_right (q : QuaternionGroup 2) : movement (rightEmbedding q) = rightMap q := by
  change rawValue (rightRaw q) = rightMap q
  have ht : (1 : C2) ≠ turn := by decide +kernel
  simp [rawValue, rightRaw, ht]

theorem movement_z : movement QuaternionSwapModel.z = z := by
  change rawValue (leftRaw (QuaternionGroup.a 2)) = z
  decide +kernel

theorem movement_swap : movement QuaternionSwapModel.swap = swap := by
  change rawValue swapRaw = swap
  decide +kernel

theorem movement_bit_zero : movement (MarkedCubic.bit 0) = markedLeftI * markedRightI := by
  change rawValue (sixteenRaw (basisBit 0)) = markedLeftI * markedRightI
  decide +kernel

theorem movement_bit_one : movement (MarkedCubic.bit 1) = v := by
  change rawValue (sixteenRaw (basisBit 1)) = v
  decide +kernel

theorem movement_bit_two : movement (MarkedCubic.bit 2) = z := by
  rw [MarkedCubic.bit_two, movement_z]

theorem movement_bit_three : movement (MarkedCubic.bit 3) = swap := by
  change rawValue (sixteenRaw (basisBit 3)) = swap
  decide +kernel

theorem movement_plane : MarkedCubic.markedPlane.map movement = natural := by
  rw [MarkedCubic.markedPlane_eq_bits, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, movement_bit_two, movement_bit_one]
  rfl

theorem extra_square : extra * extra = 1 := by decide +kernel

theorem extra_outside : extra ∉ movement.range := by
  rintro ⟨q,hq⟩
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter q
  have h : ∀ w : Raw, rawValue w ≠ extra := by decide +kernel
  exact h w hq

theorem extra_left (q : QuaternionGroup 2) :
    extra * leftMap q * extra⁻¹ = leftMap (MarkedSylow.quaternionFlip q) := by
  have h : ∀ q, extra * leftMap q * extra⁻¹ = leftMap (MarkedSylow.quaternionFlip q) := by
    decide +kernel
  exact h q

theorem extra_right (q : QuaternionGroup 2) :
    extra * rightMap q * extra⁻¹ = rightMap (MarkedSylow.quaternionFlip q) := by
  have h : ∀ q, extra * rightMap q * extra⁻¹ = rightMap (MarkedSylow.quaternionFlip q) := by
    decide +kernel
  exact h q

theorem extra_swap : extra * swap * extra⁻¹ = z * swap := by decide +kernel

theorem extra_conjugation (w : Raw) :
    extra * movement (projection w) * extra⁻¹ = movement (projection (MarkedSylow.twist w)) := by
  have hz : rawMap (leftRaw (QuaternionGroup.a 2)) = z := movement_z
  have hzl : leftMap (QuaternionGroup.a 2) = z := (movement_left _).symm.trans movement_z
  have hzr : rightMap (QuaternionGroup.a 2) = z := by
    rw [← movement_right, shared_involution, movement_z]
  have hc (q r : QuaternionGroup 2) :
      z * (leftMap q * rightMap r) = (leftMap q * rightMap r) * z := by
    have hl : z * leftMap q = leftMap q * z := by rw [← hzr, ← left_right_commute]
    have hr : z * rightMap r = rightMap r * z := by rw [← hzl, left_right_commute]
    rw [← mul_assoc, hl, mul_assoc, hr, ← mul_assoc]
  have hm (a b : Carrier) : extra * (a*b) * extra⁻¹ =
      (extra*a*extra⁻¹) * (extra*b*extra⁻¹) := by group
  change extra * rawValue w * extra⁻¹ = rawMap (MarkedSylow.twist w)
  rw [MarkedSylow.twist, map_mul, map_pow, hz]
  change extra * rawValue w * extra⁻¹ = z ^ w.right.toAdd.val *
    rawValue ⟨fun a => MarkedSylow.quaternionFlip (w.left a), w.right⟩
  have hr : w.right = 1 ∨ w.right = turn := by
    have h : ∀ r : C2, r = 1 ∨ r = turn := by decide +kernel
    exact h w.right
  have ht : turn ≠ 1 := by decide +kernel
  rcases hr with hr | hr <;> simp only [rawValue, hr, ht, ↓reduceIte, mul_one]
  · change extra * (leftMap (w.left 1) * rightMap (w.left turn)) * extra⁻¹ =
      z ^ 0 * (leftMap (MarkedSylow.quaternionFlip (w.left 1)) *
        rightMap (MarkedSylow.quaternionFlip (w.left turn)))
    rw [pow_zero, one_mul, hm, extra_left, extra_right]
  · change extra * (leftMap (w.left 1) * rightMap (w.left turn) * swap) * extra⁻¹ =
      z ^ 1 * (leftMap (MarkedSylow.quaternionFlip (w.left 1)) *
        rightMap (MarkedSylow.quaternionFlip (w.left turn)) * swap)
    rw [pow_one, hm, hm, extra_left, extra_right, extra_swap,
      ← mul_assoc, ← hc, mul_assoc]

def secondActor : Carrier := actor⁻¹

theorem actor_action_zero :
    secondActor * movement (MarkedCubic.bit 0) * secondActor⁻¹ = movement (MarkedCubic.bit 0) := by
  rw [movement_bit_zero]
  decide +kernel

theorem actor_action_one :
    secondActor * movement (MarkedCubic.bit 1) * secondActor⁻¹ = movement (MarkedCubic.bit 1 * MarkedCubic.bit 2) := by
  rw [map_mul, movement_bit_one, movement_bit_two]
  decide +kernel

theorem actor_action_two :
    secondActor * movement (MarkedCubic.bit 2) * secondActor⁻¹ = movement (MarkedCubic.bit 1) := by
  rw [movement_bit_one, movement_bit_two]
  decide +kernel

theorem actor_action_three :
    secondActor * movement (MarkedCubic.bit 3) * secondActor⁻¹ = movement (MarkedCubic.bit 1 * MarkedCubic.bit 3) := by
  rw [map_mul, movement_bit_one, movement_bit_three]
  decide +kernel

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
