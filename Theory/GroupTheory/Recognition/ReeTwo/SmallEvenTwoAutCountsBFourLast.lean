module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesBFour
public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates
public import Theory.SpecificGroups.ReeTwo.EvenCoordinates

/-!
# Intrinsic rank-four fiber counts for the last two small even candidates

For rows 5 and 6 (original indices 26 and 37), the carrier equations give
seven independent binary parameters. Solving the fixed quadratic quotient
coordinates leaves three independent parameters in every fiber. The resulting
bijections enumerate the exact candidate and its fibers, conditional only on
the separately supplied carrier certificate.

The polynomial multiplication law for the even complement computes squares,
fourth powers, and commuting pairs. Transport through the candidate bijection
therefore counts centralizers inside the candidate itself. Kernel reduction
checks the three prescribed tests on each eight-element fiber.

Source: Shinoda (1975), (2.3), pp. 81–82, with the internal coordinate convention
of `SmallEvenTwoAutCoordinatesBFour` and the proved law in `EvenCoordinates`.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

private abbrev Bits := Fin 7 → ZMod 2

private def idx (i : Fin 2) : Fin 7 := ⟨5 + i.val, by omega⟩

private def parityBit (i : Fin 2) (w : Bits) : ZMod 2 :=
  if i = 0 then w 1 + w 2 else w 0

private def core (i : Fin 2) (w : Bits) : Core :=
  if i = 0 then
    ⟨w 0, 0, w 1, w 2, w 1, w 3, w 0 + w 1 + w 2 + w 3, w 4, w 5, w 6⟩
  else
    ⟨0, w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6⟩

private def elem (i : Fin 2) (w : Bits) : SylowModel :=
  evenElement (parityBit i w) (core i w)

private def read (i : Fin 2) (x : SylowModel) : Bits :=
  if i = 0 then ![x.left.b0, x.left.b2, x.left.b3, x.left.b5,
    x.left.b7, x.left.b8, x.left.b9]
  else ![x.left.b1, x.left.b3, x.left.b4, x.left.b6,
    x.left.b7, x.left.b8, x.left.b9]

private theorem mem_elem : ∀ i w, rankFourCarrier (idx i) (elem i w) := by
  intro i w
  fin_cases i <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem read_elem : ∀ i w, read i (elem i w) = w := by
  intro i w
  funext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem elem_read : ∀ i x, rankFourCarrier (idx i) x → elem i (read i x) = x := by
  intro i x hx
  fin_cases i
  · change x.right.toAdd = 2 * ((x.left.b2 + x.left.b3).val : ZMod 4) ∧
      x.left.b1 = 0 ∧ x.left.b4 = x.left.b2 ∧
      x.left.b6 = x.left.b0 + x.left.b2 + x.left.b3 + x.left.b5 at hx
    apply SemidirectProduct.ext
    · apply Core.ext <;> dsimp [elem, core, read, evenElement] <;> simp_all
    · exact congrArg Multiplicative.ofAdd hx.1.symm
  · change x.right.toAdd = 2 * (x.left.b1.val : ZMod 4) ∧
      x.left.b0 = 0 ∧ x.left.b2 = 0 ∧ x.left.b5 = x.left.b4 at hx
    apply SemidirectProduct.ext
    · apply Core.ext <;> dsimp [elem, core, read, evenElement] <;> simp_all
    · exact congrArg Multiplicative.ofAdd hx.1.symm

private def equiv (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x) :
    Bits ≃ smallEvenCandidate (rankFourIndex (idx i)) where
  toFun w := ⟨elem i w, (h _).mpr (mem_elem i w)⟩
  invFun x := read i x.val
  left_inv := read_elem i
  right_inv x := Subtype.ext (elem_read i x.val ((h _).mp x.property))

private def productCore (i : Fin 2) (w z : Bits) : Core :=
  Core.mul (core i w) (if parityBit i w = 0 then core i z else evenCoreAction (core i z))

private theorem elem_mul (i : Fin 2) (w z : Bits) :
    elem i w * elem i z = evenElement (parityBit i w + parityBit i z) (productCore i w z) :=
  evenElement_mul _ _ _ _

private theorem comm_iff (i : Fin 2) (w z : Bits) :
    elem i w * elem i z = elem i z * elem i w ↔ productCore i w z = productCore i z w := by
  rw [elem_mul, elem_mul]
  constructor
  · exact fun h => congrArg SemidirectProduct.left h
  · intro h
    rw [h, add_comm]

-- Enumerate binary parameters by a small integer, avoiding a large function finset.

private def bits (n : Fin 128) : Bits :=
  ![(n.val : ZMod 2), (n.val / 2 : ℕ), (n.val / 4 : ℕ), (n.val / 8 : ℕ),
    (n.val / 16 : ℕ), (n.val / 32 : ℕ), (n.val / 64 : ℕ)]

private def number (w : Bits) : Fin 128 :=
  Fin.ofNat 128 ((w 0).val + 2*(w 1).val + 4*(w 2).val + 8*(w 3).val +
    16*(w 4).val + 32*(w 5).val + 64*(w 6).val)

private def bitsEquiv : Fin 128 ≃ Bits where
  toFun := bits
  invFun := number
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def cent (i : Fin 2) (w : Bits) : ℕ :=
  (Finset.univ.filter (fun n : Fin 128 => productCore i (bits n) w = productCore i w (bits n))).card

private theorem cent_eq (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x)
    (w : Bits) : MulAut.commutingCard (equiv i h w) = cent i w := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (bitsEquiv.trans (equiv i h))]
  unfold cent
  congr 1
  apply Finset.filter_congr
  intro z _
  exact Subtype.ext_iff.trans (comm_iff i (bits z) w)

private abbrev Tail := Fin 3 → ZMod 2

private def fiber (i : Fin 2) (v : Binary 4) (u : Tail) : Bits :=
  let a := v.toAdd 0
  let b := v.toAdd 1
  let c := v.toAdd 2
  let d := v.toAdd 3
  if i = 0 then
    ![c+b+d, u 0, d+u 0, a+b+d, u 1, a+(u 0)*(d+u 0)+d, u 2]
  else
    ![d, b+d, u 0, a+c+b+d, c+d*(u 0)+d, u 1, u 2]

private def tail (i : Fin 2) (w : Bits) : Tail :=
  if i = 0 then ![w 1, w 4, w 6] else ![w 2, w 5, w 6]

private theorem fiber_coordinates : ∀ i v u,
    rankFourCoordinates (idx i) (elem i (fiber i v u)) = v := by
  intro i v u
  change (rankFourCoordinates (idx i) (elem i (fiber i v u))).toAdd = v.toAdd
  funext j
  fin_cases i <;> fin_cases j <;>
    dsimp [rankFourCoordinates, idx, elem, evenElement, core, fiber] <;> ring_nf <;> reduce_mod_char

private theorem tail_fiber : ∀ i v u, tail i (fiber i v u) = u := by
  intro i v u
  funext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem fiber_tail : ∀ i w,
    fiber i (rankFourCoordinates (idx i) (elem i w)) (tail i w) = w := by
  intro i w
  funext j
  fin_cases i <;> fin_cases j <;>
    dsimp [fiber, rankFourCoordinates, idx, elem, evenElement, core, tail] <;> ring_nf <;> reduce_mod_char

private def fiberEquiv (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x)
    (v : Binary 4) : Tail ≃ {x : smallEvenCandidate (rankFourIndex (idx i)) //
      rankFourMap (idx i) x = v} where
  toFun u := ⟨equiv i h (fiber i v u), fiber_coordinates i v u⟩
  invFun x := tail i ((equiv i h).symm x.val)
  left_inv u := by
    change tail i ((equiv i h).symm (equiv i h (fiber i v u))) = u
    rw [Equiv.symm_apply_apply, tail_fiber]
  right_inv x := by
    apply Subtype.ext
    apply (equiv i h).symm.injective
    change (equiv i h).symm (equiv i h (fiber i v (tail i ((equiv i h).symm x.val)))) = _
    rw [Equiv.symm_apply_apply]
    have hx : rankFourCoordinates (idx i) (elem i ((equiv i h).symm x.val)) = v := by
      change rankFourMap (idx i) (equiv i h ((equiv i h).symm x.val)) = v
      rw [Equiv.apply_symm_apply]
      exact x.property
    simpa only [hx] using fiber_tail i ((equiv i h).symm x.val)


private def square (i : Fin 2) (w : Bits) : Core := productCore i w w

private theorem elem_square (i : Fin 2) (w : Bits) :
    elem i w ^ 2 = evenElement 0 (square i w) := by
  rw [pow_two, elem_mul]
  rw [show parityBit i w + parityBit i w = 0 from
    (by decide : ∀ t : ZMod 2, t+t=0) _]
  rfl

private theorem elem_fourth (i : Fin 2) (w : Bits) :
    elem i w ^ 4 = evenElement 0 (Core.mul (square i w) (square i w)) := by
  change elem i w ^ (2 * 2) = _
  rw [pow_mul, elem_square, pow_two, evenElement_mul]
  rfl

private theorem even_zero_eq_one (c : Core) : evenElement 0 c = 1 ↔ c = 1 := by
  constructor
  · exact fun h => congrArg SemidirectProduct.left h
  · rintro rfl
    rfl

private theorem elem_eq_one (i : Fin 2) (w : Bits) :
    elem i w = 1 ↔ parityBit i w = 0 ∧ core i w = 1 := by
  have ht : ∀ t : ZMod 2,
      (Multiplicative.ofAdd (2 * t.val) : FiveFour.Cyclic 4) = 1 ↔ t = 0 := by decide
  constructor
  · intro h
    exact ⟨(ht _).mp (congrArg SemidirectProduct.right h),
      congrArg SemidirectProduct.left h⟩
  · rintro ⟨hp, hc⟩
    change evenElement (parityBit i w) (core i w) = 1
    rw [hp, hc]
    rfl

private theorem order_four_iff {G : Type*} [Group G] (x : G) :
    orderOf x = 4 ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    constructor
    · rw [← h]; exact pow_orderOf_eq_one x
    · intro hh
      have hd := orderOf_dvd_of_pow_eq_one hh
      rw [h] at hd
      norm_num at hd
  · rintro ⟨h4, h2⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4

private def test (i : Fin 2) (j : Fin 3) (w : Bits) : Prop :=
  (if i = 0 then square i w = 1 ∧ ¬(parityBit i w = 0 ∧ core i w = 1)
    else Core.mul (square i w) (square i w) = 1 ∧ square i w ≠ 1) ∧
    cent i w = (rankFourTests (idx i) j).2.1

private instance (i : Fin 2) (j : Fin 3) (w : Bits) : Decidable (test i j w) := by
  unfold test
  infer_instance

private theorem test_iff (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x)
    (j : Fin 3) (w : Bits) :
    MulAut.orderCentralizerTest (rankFourTests (idx i) j) (equiv i h w) ↔ test i j w := by
  rw [MulAut.orderCentralizerTest, cent_eq]
  have ho : orderOf (equiv i h w) = orderOf (elem i w) := Subgroup.orderOf_mk _ _
  rw [ho]
  have hz : (rankFourTests (idx i) j).2.2 = 0 := (by decide : ∀ i j,
    (rankFourTests (idx i) j).2.2 = 0) i j
  simp only [hz, true_or, and_true]
  unfold test
  have ht : (rankFourTests (idx i) j).1 = if i = 0 then 2 else 4 :=
    (by decide : ∀ i j, (rankFourTests (idx i) j).1 = if i = 0 then 2 else 4) i j
  rw [ht]
  by_cases hi : i = 0
  · simp only [if_pos hi]
    simp only [orderOf_eq_prime_iff, elem_square, even_zero_eq_one, ne_eq, elem_eq_one]
  · simp only [if_neg hi]
    simp only [order_four_iff, elem_square, elem_fourth, ne_eq, even_zero_eq_one]

private def count (i : Fin 2) (j : Fin 3) (v : Binary 4) : ℕ :=
  (Finset.univ.filter (fun u : Tail => test i j (fiber i v u))).card

private theorem card_test (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x)
    (j : Fin 3) (v : Binary 4) :
    Nat.card {x : smallEvenCandidate (rankFourIndex (idx i)) //
      rankFourMap (idx i) x = v ∧ MulAut.orderCentralizerTest (rankFourTests (idx i) j) x} =
      count i j v := by
  calc
    _ = Nat.card {u : Tail // test i j (fiber i v u)} := by
      apply (Nat.card_congr _).symm
      exact ((fiberEquiv i h v).subtypeEquiv
        (fun u => (test_iff i h j (fiber i v u)).symm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

private def decodeV (n : Fin 16) : Binary 4 :=
  Multiplicative.ofAdd ![(n.val : ZMod 2), (n.val / 2 : ℕ),
    (n.val / 4 : ℕ), (n.val / 8 : ℕ)]

private def encodeV (v : Binary 4) : Fin 16 :=
  Fin.ofNat 16 ((v.toAdd 0).val + 2*(v.toAdd 1).val +
    4*(v.toAdd 2).val + 8*(v.toAdd 3).val)

private theorem decodeV_encodeV : ∀ v, decodeV (encodeV v) = v := by decide +kernel

set_option maxHeartbeats 32000000 in
private theorem count_certificate_fin : ∀ i n,
    (count i 0 (decodeV n), count i 1 (decodeV n), count i 2 (decodeV n)) =
      rankFourProfile (idx i) (decodeV n) := by decide +kernel

private theorem count_certificate (i : Fin 2) (v : Binary 4) :
    (count i 0 v, count i 1 v, count i 2 v) = rankFourProfile (idx i) v := by
  simpa only [decodeV_encodeV] using count_certificate_fin i (encodeV v)

private theorem profile_eq (i : Fin 2)
    (h : ∀ x, x ∈ smallEvenCandidate (rankFourIndex (idx i)) ↔ rankFourCarrier (idx i) x)
    (v : Binary 4) : rankFourCoordinateProfile (idx i) v = rankFourProfile (idx i) v := by
  unfold rankFourCoordinateProfile
  rw [card_test i h, card_test i h, card_test i h]
  exact count_certificate i v

/-- The last two fixed rank-four coordinate systems realize all three intrinsic
order/centralizer counts, assuming the exact carrier certificate. -/
public theorem rankFourCoordinateProfile_last (i : Fin 7) (hi : 5 ≤ i.val)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex i) ↔ rankFourCarrier i x) :
    ∀ v, rankFourCoordinateProfile i v = rankFourProfile i v := by
  let k : Fin 2 := ⟨i.val - 5, by omega⟩
  have he : idx k = i := by apply Fin.ext; dsimp [idx, k]; omega
  intro v
  simpa only [he] using profile_eq k (by simpa only [he] using hcarrier) v

end ReeTwo.SylowModel.SmallEvenAutB
