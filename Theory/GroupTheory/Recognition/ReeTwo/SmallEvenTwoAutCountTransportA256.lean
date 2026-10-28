module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesA256
public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates

/-!
# Intrinsic count transport for the order-256 small even candidates

Eight bits parametrize each exact candidate. Powers reduce element orders two
and four to polynomial equations, and a proved Boolean encoding evaluates
commuting inside the candidate. An explicit duplicate-free list realizes the
finite counts without repeatedly rebuilding function finsets. The polynomial
identities are proved algebraically; no external enumeration is trusted.

Source: Shinoda (1975), (2.3), pp. 81–82, through the coordinate and basis
conventions of SmallEvenTwoAutCoordinatesA256 and SmallEvenAutProfilesA.
-/

namespace ReeTwo.SylowModel.A256Count
open ReeTwo.SmallEvenAutProfilesA
set_option maxRecDepth 32768
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096

@[expose] public def bits (n : Fin 256) : A256Bits :=
  ![(n.val : ZMod 2), (n.val / 2 : ℕ), (n.val / 4 : ℕ), (n.val / 8 : ℕ),
    (n.val / 16 : ℕ), (n.val / 32 : ℕ), (n.val / 64 : ℕ), (n.val / 128 : ℕ)]

@[expose] public def number (w : A256Bits) : Fin 256 :=
  Fin.ofNat 256 ((w 0).val + 2*(w 1).val + 4*(w 2).val + 8*(w 3).val +
    16*(w 4).val + 32*(w 5).val + 64*(w 6).val + 128*(w 7).val)

@[expose] public def bitsEquiv : Fin 256 ≃ A256Bits where
  toFun := bits
  invFun := number
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def square (i : Fin 11) (w : A256Bits) : EvenPair :=
  evenPairMul (a256Pair i w) (a256Pair i w)

@[expose] public def comm (i : Fin 11) (w z : A256Bits) : Prop :=
  evenPairMul (a256Pair i w) (a256Pair i z) =
    evenPairMul (a256Pair i z) (a256Pair i w)
public instance (i : Fin 11) (w z : A256Bits) : Decidable (comm i w z) := by
  unfold comm; infer_instance

@[expose] public def cent (i : Fin 11) (w : A256Bits) : ℕ :=
  (Finset.univ.filter (fun n : Fin 256 => comm i (bits n) w)).card

public theorem cent_eq (i : Fin 11) (w : A256Bits) :
    MulAut.commutingCard (a256Equiv i w) = cent i w := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (bitsEquiv.trans (a256Equiv i))]
  unfold cent
  congr 1
  apply Finset.filter_congr
  intro n _
  change a256Element i (bits n) * a256Element i w =
    a256Element i w * a256Element i (bits n) ↔ _
  rw [Subtype.ext_iff]
  change evenPairElement (a256Pair i (bits n)) * evenPairElement (a256Pair i w) =
    evenPairElement (a256Pair i w) * evenPairElement (a256Pair i (bits n)) ↔ _
  rw [← evenPairElement_mul, ← evenPairElement_mul, evenPairElement_injective.eq_iff]
  rfl

public theorem elem_one (i : Fin 11) (w : A256Bits) :
    a256Element i w = 1 ↔ a256Pair i w = (1, 0) := by
  rw [Subtype.ext_iff]
  change evenPairElement (a256Pair i w) = evenPairElement (1, 0) ↔ _
  exact evenPairElement_injective.eq_iff

public theorem elem_square (i : Fin 11) (w : A256Bits) :
    a256Element i w ^ 2 = 1 ↔ square i w = (1, 0) := by
  rw [pow_two, Subtype.ext_iff]
  change evenPairElement (a256Pair i w) * evenPairElement (a256Pair i w) =
    evenPairElement (1, 0) ↔ _
  rw [← evenPairElement_mul, evenPairElement_injective.eq_iff]
  rfl

public theorem elem_fourth (i : Fin 11) (w : A256Bits) :
    a256Element i w ^ 4 = 1 ↔ evenPairMul (square i w) (square i w) = (1, 0) := by
  change a256Element i w ^ (2 * 2) = 1 ↔ _
  rw [pow_mul, pow_two, pow_two, Subtype.ext_iff]
  change (evenPairElement (a256Pair i w) * evenPairElement (a256Pair i w)) *
    (evenPairElement (a256Pair i w) * evenPairElement (a256Pair i w)) =
    evenPairElement (1, 0) ↔ _
  rw [← evenPairElement_mul, ← evenPairElement_mul, evenPairElement_injective.eq_iff]
  rfl

public theorem order_four_iff {G : Type*} [Group G] (x : G) :
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

@[expose] public def test (i : Fin 11) (j : Fin 2) (w : A256Bits) : Prop :=
  (if j = 0 then square i w = (1, 0) ∧ a256Pair i w ≠ (1, 0)
    else evenPairMul (square i w) (square i w) = (1, 0) ∧ square i w ≠ (1, 0)) ∧
    cent i w = (fourTests (a256Row i) j).2.1
public instance (i : Fin 11) (j : Fin 2) (w : A256Bits) : Decidable (test i j w) := by
  unfold test; infer_instance

public theorem test_iff (i : Fin 11) (j : Fin 2) (w : A256Bits) :
    MulAut.orderCentralizerTest (fourTests (a256Row i) j) (a256Equiv i w) ↔
      test i j w := by
  rw [MulAut.orderCentralizerTest, cent_eq]
  have hz : (fourTests (a256Row i) j).2.2 = 0 :=
    (by decide : ∀ i j, (fourTests (a256Row i) j).2.2 = 0) i j
  have ht : (fourTests (a256Row i) j).1 = if j = 0 then 2 else 4 :=
    (by decide : ∀ i j, (fourTests (a256Row i) j).1 = if j = 0 then 2 else 4) i j
  simp only [hz, true_or, and_true, ht]
  change (orderOf (a256Element i w) = (if j = 0 then 2 else 4) ∧ _) ↔ _
  unfold test
  split_ifs with hj
  · simp only [orderOf_eq_prime_iff, elem_square, ne_eq, elem_one]
  · simp only [order_four_iff, elem_square, elem_fourth, ne_eq]

@[expose] public def count (i : Fin 11) (j : Fin 2) (v : FourQuotient) : ℕ :=
  (Finset.univ.filter (fun n : Fin 256 =>
    a256Coordinates i (bits n) = v ∧ test i j (bits n))).card

public theorem card_test (i : Fin 11) (j : Fin 2) (v : FourQuotient) :
    Nat.card {x : smallEvenCandidate (a256Index i) //
      a256Map i x = v ∧ MulAut.orderCentralizerTest (fourTests (a256Row i) j) x} =
      count i j v := by
  calc
    _ = Nat.card {n : Fin 256 // a256Coordinates i (bits n) = v ∧ test i j (bits n)} := by
      apply (Nat.card_congr _).symm
      refine (bitsEquiv.trans (a256Equiv i)).subtypeEquiv (fun n => ?_)
      change (_ ∧ _) ↔ (a256Coordinates i ((a256Equiv i).symm
        (a256Equiv i (bits n))) = v ∧ _)
      rw [Equiv.symm_apply_apply]
      change (_ ∧ _) ↔ (_ ∧ MulAut.orderCentralizerTest _ (a256Equiv i (bits n)))
      rw [test_iff]
    _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl

@[expose] public def decodeV (n : Fin 16) : FourQuotient :=
  Multiplicative.ofAdd ![(n.val : ZMod 2), (n.val / 2 : ℕ),
    (n.val / 4 : ℕ), (n.val / 8 : ℕ)]

@[expose] public def encodeV (v : FourQuotient) : Fin 16 :=
  Fin.ofNat 16 ((v.toAdd 0).val + 2*(v.toAdd 1).val +
    4*(v.toAdd 2).val + 8*(v.toAdd 3).val)

public theorem decodeV_encodeV : ∀ v, decodeV (encodeV v) = v := by decide +kernel


@[expose] public def polyAction (t : ZMod 2) (x : Core) : Core where
  b0 := x.b0 + t * ((evenCoreAction x).b0 + x.b0)
  b1 := x.b1 + t * ((evenCoreAction x).b1 + x.b1)
  b2 := x.b2 + t * ((evenCoreAction x).b2 + x.b2)
  b3 := x.b3 + t * ((evenCoreAction x).b3 + x.b3)
  b4 := x.b4 + t * ((evenCoreAction x).b4 + x.b4)
  b5 := x.b5 + t * ((evenCoreAction x).b5 + x.b5)
  b6 := x.b6 + t * ((evenCoreAction x).b6 + x.b6)
  b7 := x.b7 + t * ((evenCoreAction x).b7 + x.b7)
  b8 := x.b8 + t * ((evenCoreAction x).b8 + x.b8)
  b9 := x.b9 + t * ((evenCoreAction x).b9 + x.b9)

public theorem polyAction_eq (t : ZMod 2) (x : Core) :
    polyAction t x = if t = 0 then x else evenCoreAction x := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · rw [if_pos rfl]
    apply Core.ext <;> simp only [polyAction, zero_mul, add_zero]
  · rw [if_neg (show (1 : ZMod 2) ≠ 0 by decide)]
    apply Core.ext <;> simp only [polyAction, one_mul]
    all_goals exact (by decide : ∀ a b : ZMod 2, a + (b + a) = b) _ _


@[expose] public def polyMul (x y : EvenPair) : Core := Core.mul x.1 (polyAction x.2 y.1)

public theorem pairMul_fst (x y : EvenPair) : (evenPairMul x y).1 = polyMul x y := by
  rw [polyMul, polyAction_eq]
  rfl

@[expose] public def obstruction (i : Fin 11) (w z : A256Bits) : Fin 10 → ZMod 2 :=
  (![
    ![0, 0, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, 0, 0, w 1 * w 2 * z 0 + w 0 * w 1 * z 1 + w 2 * z 1 + w 3 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 1 * z 2 + w 0 * w 1 * z 2 + w 3 * z 2 + w 0 * z 1 * z 2 + w 1 * z 3 + w 2 * z 3, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 4 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 0 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 1 * z 3 + w 2 * z 3 + w 1 * z 4 + w 2 * z 4, w 1 * z 0 + w 1 * w 3 * z 0 + w 2 * w 3 * z 0 + w 1 * w 4 * z 0 + w 2 * w 4 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * w 1 * z 2 + w 3 * z 2 + w 4 * z 2 + w 2 * z 3 + w 0 * z 1 * z 3 + w 0 * z 2 * z 3 + w 2 * z 4 + w 0 * z 1 * z 4 + w 0 * z 2 * z 4 + w 0 * z 6],
    ![0, 0, 0, 0, 0, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 1 * z 0 + w 0 * z 1 + w 2 * z 1 + w 1 * z 2, 0, w 1 * z 0 + w 2 * z 0 + w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 0 * w 2 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 0 * z 1 * z 2 + w 1 * z 3 + w 2 * z 4 + w 0 * z 6],
    ![0, 0, 0, 0, 0, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, 0, w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2, w 2 * z 1 + w 1 * z 2, w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * w 2 * z 1 + w 0 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 2 * z 4 + w 0 * z 6],
    ![0, 0, 0, 0, 0, w 1 * z 0 + w 0 * z 1, w 2 * z 0 + w 0 * z 2, w 2 * z 0 + w 0 * z 2, w 2 * z 1 + w 1 * z 2, w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * w 2 * z 1 + w 3 * z 2 + w 1 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 0 * z 6],
    ![0, 0, 0, 0, 0, w 1 * z 0 + w 0 * z 1, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 2 * z 0 + w 0 * z 2, 0, w 1 * z 0 + w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 4 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * w 1 * z 2 + w 3 * z 2 + w 1 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 1 * z 4 + w 0 * z 6],
    ![0, 0, 0, 0, 0, 0, 0, w 2 * z 0 + w 0 * z 2, w 2 * z 0 + w 0 * z 2, w 2 * z 0 + w 5 * z 0 + w 4 * z 1 + w 0 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 4 + w 0 * z 5],
    ![0, 0, 0, 0, 0, 0, 0, w 2 * z 0 + w 3 * z 0 + w 0 * z 2 + w 0 * z 3, w 2 * z 0 + w 3 * z 0 + w 4 * z 0 + w 0 * z 2 + w 0 * z 3 + w 0 * z 4, w 2 * z 0 + w 3 * z 0 + w 0 * w 3 * z 0 + w 5 * z 0 + w 4 * z 1 + w 0 * z 2 + w 3 * z 2 + w 0 * z 3 + w 2 * z 3 + w 0 * z 0 * z 3 + w 1 * z 4 + w 0 * z 5],
    ![0, 0, 0, 0, 0, 0, w 1 * z 0 + w 0 * z 1 + w 2 * z 1 + w 1 * z 2, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2, 0, w 2 * z 0 + w 6 * z 0 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 5 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 1 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 1 * z 2 + w 1 * z 3 + w 2 * z 3 + w 2 * z 4 + w 1 * z 5 + w 0 * z 6],
    ![0, 0, 0, 0, 0, 0, w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2, w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2, 0, w 1 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 2 * z 1 + w 4 * z 1 + w 5 * z 1 + w 1 * z 0 * z 1 + w 1 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 4 + w 1 * z 5 + w 0 * z 6],
    ![0, 0, 0, 0, 0, 0, w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2, 0, 0, w 2 * z 0 + w 6 * z 0 + w 2 * z 1 + w 5 * z 1 + w 0 * z 2 + w 1 * z 2 + w 0 * w 2 * z 2 + w 1 * w 2 * z 2 + w 4 * z 2 + w 2 * z 0 * z 2 + w 2 * z 1 * z 2 + w 2 * z 4 + w 1 * z 5 + w 0 * z 6],
    ![0, 0, 0, 0, 0, 0, w 2 * z 0 + w 0 * z 2, w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2, w 2 * z 1 + w 1 * z 2, w 6 * z 0 + w 2 * z 1 + w 5 * z 1 + w 2 * z 0 * z 1 + w 1 * z 2 + w 0 * w 1 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 5 + w 0 * z 6]]) i

public theorem obstruction_eq_0 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 0 w) (a256Pair 0 z)) +
      Core.coords (polyMul (a256Pair 0 z) (a256Pair 0 w)) = obstruction 0 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b2 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b3 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b4 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b6 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 1 * w 2 * z 0 + w 0 * w 1 * z 1 + w 2 * z 1 + w 3 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 1 * z 2 + w 0 * w 1 * z 2 + w 3 * z 2 + w 0 * z 1 * z 2 + w 1 * z 3 + w 2 * z 3
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 4 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 0 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 1 * z 3 + w 2 * z 3 + w 1 * z 4 + w 2 * z 4
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 1 + w 2) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 1 + z 2) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * z 0 + w 1 * w 3 * z 0 + w 2 * w 3 * z 0 + w 1 * w 4 * z 0 + w 2 * w 4 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * w 1 * z 2 + w 3 * z 2 + w 4 * z 2 + w 2 * z 3 + w 0 * z 1 * z 3 + w 0 * z 2 * z 3 + w 2 * z 4 + w 0 * z 1 * z 4 + w 0 * z 2 * z 4 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_1 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 1 w) (a256Pair 1 z)) +
      Core.coords (polyMul (a256Pair 1 z) (a256Pair 1 w)) = obstruction 1 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b5 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 1 * z 0 + w 0 * z 1 + w 2 * z 1 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b8 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 1, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * z 0 + w 2 * z 0 + w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 0 * w 2 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 0 * z 1 * z 2 + w 1 * z 3 + w 2 * z 4 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_2 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 2 w) (a256Pair 2 z)) +
      Core.coords (polyMul (a256Pair 2 z) (a256Pair 2 w)) = obstruction 2 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 2 * z 1 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, 0, z 1, z 2, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * w 2 * z 1 + w 0 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 2 * z 4 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_3 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 3 w) (a256Pair 3 z)) +
      Core.coords (polyMul (a256Pair 3 z) (a256Pair 3 w)) = obstruction 3 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = w 1 * z 0 + w 0 * z 1
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 2 * z 1 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, 0, z 1, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, w 1, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * w 2 * z 1 + w 3 * z 2 + w 1 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_4 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 4 w) (a256Pair 4 z)) +
      Core.coords (polyMul (a256Pair 4 z) (a256Pair 4 w)) = obstruction 4 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = w 1 * z 0 + w 0 * z 1
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * z 0 + w 1 * w 2 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 4 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * w 1 * z 2 + w 3 * z 2 + w 1 * z 0 * z 2 + w 0 * z 1 * z 2 + w 2 * z 3 + w 1 * z 4 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_5 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 5 w) (a256Pair 5 z)) +
      Core.coords (polyMul (a256Pair 5 z) (a256Pair 5 w)) = obstruction 5 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 2 * z 0 + w 5 * z 0 + w 4 * z 1 + w 0 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 4 + w 0 * z 5
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_6 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 6 w) (a256Pair 6 z)) +
      Core.coords (polyMul (a256Pair 6 z) (a256Pair 6 w)) = obstruction 6 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 3 * z 0 + w 0 * z 2 + w 0 * z 3
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 2 * z 0 + w 3 * z 0 + w 4 * z 0 + w 0 * z 2 + w 0 * z 3 + w 0 * z 4
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (w 0) ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨0, z 0, 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (z 0) ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 2 * z 0 + w 3 * z 0 + w 0 * w 3 * z 0 + w 5 * z 0 + w 4 * z 1 + w 0 * z 2 + w 3 * z 2 + w 0 * z 3 + w 2 * z 3 + w 0 * z 0 * z 3 + w 1 * z 4 + w 0 * z 5
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_7 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 7 w) (a256Pair 7 z)) +
      Core.coords (polyMul (a256Pair 7 z) (a256Pair 7 w)) = obstruction 7 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 1 * z 0 + w 0 * z 1 + w 2 * z 1 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, z 1 + z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, w 1 + w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 2 * z 0 + w 6 * z 0 + w 0 * w 1 * z 1 + w 0 * w 2 * z 1 + w 3 * z 1 + w 5 * z 1 + w 1 * z 0 * z 1 + w 2 * z 0 * z 1 + w 0 * z 2 + w 0 * w 1 * z 2 + w 1 * w 2 * z 2 + w 3 * z 2 + w 4 * z 2 + w 1 * z 0 * z 2 + w 2 * z 1 * z 2 + w 1 * z 3 + w 2 * z 3 + w 2 * z 4 + w 1 * z 5 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_8 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 8 w) (a256Pair 8 z)) +
      Core.coords (polyMul (a256Pair 8 z) (a256Pair 8 w)) = obstruction 8 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 1 * z 0 + w 2 * z 0 + w 0 * z 1 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, z 1, z 1, z 1, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 1, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 1 * z 0 + w 6 * z 0 + w 0 * z 1 + w 0 * w 1 * z 1 + w 2 * z 1 + w 4 * z 1 + w 5 * z 1 + w 1 * z 0 * z 1 + w 1 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 4 + w 1 * z 5 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_9 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 9 w) (a256Pair 9 z)) +
      Core.coords (polyMul (a256Pair 9 z) (a256Pair 9 w)) = obstruction 9 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b7 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b8 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, z 1, z 2, z 2, 0, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, w 2, w 2, 0, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 2 * z 0 + w 6 * z 0 + w 2 * z 1 + w 5 * z 1 + w 0 * z 2 + w 1 * z 2 + w 0 * w 2 * z 2 + w 1 * w 2 * z 2 + w 4 * z 2 + w 2 * z 0 * z 2 + w 2 * z 1 * z 2 + w 2 * z 4 + w 1 * z 5 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq_10 (w z : A256Bits) :
    Core.coords (polyMul (a256Pair 10 w) (a256Pair 10 z)) +
      Core.coords (polyMul (a256Pair 10 z) (a256Pair 10 w)) = obstruction 10 w z := by
  funext k; fin_cases k
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b0 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b0 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b1 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b1 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b2 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b2 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b3 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b3 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b4 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b4 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b5 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b5 = 0
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b6 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b6 = w 2 * z 0 + w 0 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b7 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b7 = w 2 * z 0 + w 2 * z 1 + w 0 * z 2 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b8 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b8 = w 2 * z 1 + w 1 * z 2
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char
  · change (Core.mul ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩ (polyAction (0) ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩)).b9 +
      (Core.mul ⟨z 0, z 1, 0, 0, z 2, z 3, z 4, z 5, z 6, z 7⟩ (polyAction (0) ⟨w 0, w 1, 0, 0, w 2, w 3, w 4, w 5, w 6, w 7⟩)).b9 = w 6 * z 0 + w 2 * z 1 + w 5 * z 1 + w 2 * z 0 * z 1 + w 1 * z 2 + w 0 * w 1 * z 2 + w 3 * z 2 + w 2 * z 3 + w 1 * z 5 + w 0 * z 6
    simp only [polyAction, evenCoreAction, Core.mul]
    ring_nf
    all_goals reduce_mod_char
    all_goals try simp only [show ∀ a : ZMod 2, a ^ 2 = a from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

public theorem obstruction_eq (i : Fin 11) (w z : A256Bits) :
    Core.coords (polyMul (a256Pair i w) (a256Pair i z)) +
      Core.coords (polyMul (a256Pair i z) (a256Pair i w)) = obstruction i w z := by
  fin_cases i
  · exact obstruction_eq_0 w z
  · exact obstruction_eq_1 w z
  · exact obstruction_eq_2 w z
  · exact obstruction_eq_3 w z
  · exact obstruction_eq_4 w z
  · exact obstruction_eq_5 w z
  · exact obstruction_eq_6 w z
  · exact obstruction_eq_7 w z
  · exact obstruction_eq_8 w z
  · exact obstruction_eq_9 w z
  · exact obstruction_eq_10 w z

public theorem comm_obstruction (i : Fin 11) (w z : A256Bits) :
    comm i w z ↔ ∀ k, obstruction i w z k = 0 := by
  rw [comm, Prod.ext_iff, pairMul_fst, pairMul_fst]
  simp only [evenPairMul, add_comm (a256Pair i w).2 (a256Pair i z).2, and_true]
  rw [← Core.coordinateEquiv.injective.eq_iff]
  change Core.coords _ = Core.coords _ ↔ _
  rw [funext_iff]
  have hh := congrFun (obstruction_eq i w z)
  simp only [Pi.add_apply] at hh
  simp only [← hh, show ∀ a b : ZMod 2, a + b = 0 ↔ a = b from by decide]



@[expose] public def bit (n : Fin 256) (k : Fin 8) : Bool := n.val / 2^k.val % 2 == 1
@[expose] public def zbit (b : Bool) : ZMod 2 := if b then 1 else 0
public theorem zbit_xor : ∀ a b, zbit (a ^^ b) = zbit a + zbit b := by decide +kernel
public theorem zbit_and : ∀ a b, zbit (a && b) = zbit a * zbit b := by decide +kernel
public theorem zbit_zero : ∀ a, zbit a = 0 ↔ a = false := by decide +kernel
public theorem bits_bit : ∀ n k, bits n k = zbit (bit n k) := by decide +kernel
@[expose] public def bobstruction (i : Fin 11) (w z : Fin 256) : Fin 10 → Bool :=
  (![
    ![false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), false, false, ((bit w 1) && (bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 3) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 0) && (bit z 1) && (bit z 2)) ^^ ((bit w 1) && (bit z 3)) ^^ ((bit w 2) && (bit z 3)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 3) && (bit z 1)) ^^ ((bit w 4) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 0) && (bit w 2) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 2) && (bit z 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 3)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 1) && (bit z 4)) ^^ ((bit w 2) && (bit z 4)), ((bit w 1) && (bit z 0)) ^^ ((bit w 1) && (bit w 3) && (bit z 0)) ^^ ((bit w 2) && (bit w 3) && (bit z 0)) ^^ ((bit w 1) && (bit w 4) && (bit z 0)) ^^ ((bit w 2) && (bit w 4) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 0) && (bit z 1) && (bit z 3)) ^^ ((bit w 0) && (bit z 2) && (bit z 3)) ^^ ((bit w 2) && (bit z 4)) ^^ ((bit w 0) && (bit z 1) && (bit z 4)) ^^ ((bit w 0) && (bit z 2) && (bit z 4)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 1) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)), false, ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 1) && (bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 3) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 0) && (bit w 2) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 2) && (bit z 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 1) && (bit z 2)) ^^ ((bit w 1) && (bit z 3)) ^^ ((bit w 2) && (bit z 4)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), false, ((bit w 2) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)), ((bit w 2) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)), ((bit w 1) && (bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit w 2) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 2) && (bit z 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 1) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 2) && (bit z 4)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)), ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)), ((bit w 1) && (bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 1) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), false, ((bit w 1) && (bit z 0)) ^^ ((bit w 1) && (bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 4) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 1) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 1) && (bit z 4)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, false, false, ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 5) && (bit z 0)) ^^ ((bit w 4) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 1) && (bit z 4)) ^^ ((bit w 0) && (bit z 5))],
    ![false, false, false, false, false, false, false, ((bit w 2) && (bit z 0)) ^^ ((bit w 3) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 3)), ((bit w 2) && (bit z 0)) ^^ ((bit w 3) && (bit z 0)) ^^ ((bit w 4) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 0) && (bit z 3)) ^^ ((bit w 0) && (bit z 4)), ((bit w 2) && (bit z 0)) ^^ ((bit w 3) && (bit z 0)) ^^ ((bit w 0) && (bit w 3) && (bit z 0)) ^^ ((bit w 5) && (bit z 0)) ^^ ((bit w 4) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 0) && (bit z 3)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 0) && (bit z 0) && (bit z 3)) ^^ ((bit w 1) && (bit z 4)) ^^ ((bit w 0) && (bit z 5))],
    ![false, false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)), ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)), false, ((bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 0) && (bit w 2) && (bit z 1)) ^^ ((bit w 3) && (bit z 1)) ^^ ((bit w 5) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 1) && (bit w 2) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 1) && (bit z 0) && (bit z 2)) ^^ ((bit w 2) && (bit z 1) && (bit z 2)) ^^ ((bit w 1) && (bit z 3)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 2) && (bit z 4)) ^^ ((bit w 1) && (bit z 5)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, false, ((bit w 1) && (bit z 0)) ^^ ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)), false, ((bit w 1) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 0) && (bit z 1)) ^^ ((bit w 0) && (bit w 1) && (bit z 1)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 4) && (bit z 1)) ^^ ((bit w 5) && (bit z 1)) ^^ ((bit w 1) && (bit z 0) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 1) && (bit z 4)) ^^ ((bit w 1) && (bit z 5)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, false, ((bit w 2) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)), false, false, ((bit w 2) && (bit z 0)) ^^ ((bit w 6) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 5) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)) ^^ ((bit w 0) && (bit w 2) && (bit z 2)) ^^ ((bit w 1) && (bit w 2) && (bit z 2)) ^^ ((bit w 4) && (bit z 2)) ^^ ((bit w 2) && (bit z 0) && (bit z 2)) ^^ ((bit w 2) && (bit z 1) && (bit z 2)) ^^ ((bit w 2) && (bit z 4)) ^^ ((bit w 1) && (bit z 5)) ^^ ((bit w 0) && (bit z 6))],
    ![false, false, false, false, false, false, ((bit w 2) && (bit z 0)) ^^ ((bit w 0) && (bit z 2)), ((bit w 2) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 0) && (bit z 2)) ^^ ((bit w 1) && (bit z 2)), ((bit w 2) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)), ((bit w 6) && (bit z 0)) ^^ ((bit w 2) && (bit z 1)) ^^ ((bit w 5) && (bit z 1)) ^^ ((bit w 2) && (bit z 0) && (bit z 1)) ^^ ((bit w 1) && (bit z 2)) ^^ ((bit w 0) && (bit w 1) && (bit z 2)) ^^ ((bit w 3) && (bit z 2)) ^^ ((bit w 2) && (bit z 3)) ^^ ((bit w 1) && (bit z 5)) ^^ ((bit w 0) && (bit z 6))]]) i

public theorem obstruction_bool_0 (n m : Fin 256) :
    obstruction 0 (bits n) (bits m) = fun k => zbit (bobstruction 0 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 2 * (bits m) 1 + (bits n) 3 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 1 * (bits m) 2 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 0 * (bits m) 1 * (bits m) 2 + (bits n) 1 * (bits m) 3 + (bits n) 2 * (bits m) 3 = zbit (((bit n 1) && (bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 3) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 0) && (bit m 1) && (bit m 2)) ^^ ((bit n 1) && (bit m 3)) ^^ ((bit n 2) && (bit m 3)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 3 * (bits m) 1 + (bits n) 4 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 0 * (bits n) 2 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 2 * (bits m) 0 * (bits m) 2 + (bits n) 1 * (bits m) 3 + (bits n) 2 * (bits m) 3 + (bits n) 1 * (bits m) 4 + (bits n) 2 * (bits m) 4 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 3) && (bit m 1)) ^^ ((bit n 4) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 0) && (bit n 2) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 2) && (bit m 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 3)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 1) && (bit m 4)) ^^ ((bit n 2) && (bit m 4)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 1 * (bits n) 3 * (bits m) 0 + (bits n) 2 * (bits n) 3 * (bits m) 0 + (bits n) 1 * (bits n) 4 * (bits m) 0 + (bits n) 2 * (bits n) 4 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 0 * (bits m) 1 * (bits m) 3 + (bits n) 0 * (bits m) 2 * (bits m) 3 + (bits n) 2 * (bits m) 4 + (bits n) 0 * (bits m) 1 * (bits m) 4 + (bits n) 0 * (bits m) 2 * (bits m) 4 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 1) && (bit n 3) && (bit m 0)) ^^ ((bit n 2) && (bit n 3) && (bit m 0)) ^^ ((bit n 1) && (bit n 4) && (bit m 0)) ^^ ((bit n 2) && (bit n 4) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 0) && (bit m 1) && (bit m 3)) ^^ ((bit n 0) && (bit m 2) && (bit m 3)) ^^ ((bit n 2) && (bit m 4)) ^^ ((bit n 0) && (bit m 1) && (bit m 4)) ^^ ((bit n 0) && (bit m 2) && (bit m 4)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_1 (n m : Fin 256) :
    obstruction 1 (bits n) (bits m) = fun k => zbit (bobstruction 1 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 2 * (bits m) 1 + (bits n) 1 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 1 * (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 3 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 0 * (bits n) 2 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 2 * (bits m) 0 * (bits m) 2 + (bits n) 0 * (bits m) 1 * (bits m) 2 + (bits n) 1 * (bits m) 3 + (bits n) 2 * (bits m) 4 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 1) && (bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 3) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 0) && (bit n 2) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 2) && (bit m 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 1) && (bit m 2)) ^^ ((bit n 1) && (bit m 3)) ^^ ((bit n 2) && (bit m 4)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_2 (n m : Fin 256) :
    obstruction 2 (bits n) (bits m) = fun k => zbit (bobstruction 2 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 1 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits n) 2 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 2 * (bits m) 0 * (bits m) 2 + (bits n) 0 * (bits m) 1 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 2 * (bits m) 4 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit n 2) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 2) && (bit m 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 1) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 2) && (bit m 4)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_3 (n m : Fin 256) :
    obstruction 3 (bits n) (bits m) = fun k => zbit (bobstruction 3 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 0 * (bits m) 1 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 1 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 3 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 0 * (bits m) 1 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 1) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_4 (n m : Fin 256) :
    obstruction 4 (bits n) (bits m) = fun k => zbit (bobstruction 4 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 0 * (bits m) 1 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 1 * (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 4 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 0 * (bits m) 1 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 1 * (bits m) 4 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 1) && (bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 4) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 1) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 1) && (bit m 4)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_5 (n m : Fin 256) :
    obstruction 5 (bits n) (bits m) = fun k => zbit (bobstruction 5 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 5 * (bits m) 0 + (bits n) 4 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 1 * (bits m) 4 + (bits n) 0 * (bits m) 5 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 5) && (bit m 0)) ^^ ((bit n 4) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 1) && (bit m 4)) ^^ ((bit n 0) && (bit m 5)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_6 (n m : Fin 256) :
    obstruction 6 (bits n) (bits m) = fun k => zbit (bobstruction 6 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 3 * (bits m) 0 + (bits n) 0 * (bits m) 2 + (bits n) 0 * (bits m) 3 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 3) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 3)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 3 * (bits m) 0 + (bits n) 4 * (bits m) 0 + (bits n) 0 * (bits m) 2 + (bits n) 0 * (bits m) 3 + (bits n) 0 * (bits m) 4 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 3) && (bit m 0)) ^^ ((bit n 4) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 0) && (bit m 3)) ^^ ((bit n 0) && (bit m 4)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 3 * (bits m) 0 + (bits n) 0 * (bits n) 3 * (bits m) 0 + (bits n) 5 * (bits m) 0 + (bits n) 4 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 0 * (bits m) 3 + (bits n) 2 * (bits m) 3 + (bits n) 0 * (bits m) 0 * (bits m) 3 + (bits n) 1 * (bits m) 4 + (bits n) 0 * (bits m) 5 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 3) && (bit m 0)) ^^ ((bit n 0) && (bit n 3) && (bit m 0)) ^^ ((bit n 5) && (bit m 0)) ^^ ((bit n 4) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 0) && (bit m 3)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 0) && (bit m 0) && (bit m 3)) ^^ ((bit n 1) && (bit m 4)) ^^ ((bit n 0) && (bit m 5)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_7 (n m : Fin 256) :
    obstruction 7 (bits n) (bits m) = fun k => zbit (bobstruction 7 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 2 * (bits m) 1 + (bits n) 1 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 0 * (bits n) 2 * (bits m) 1 + (bits n) 3 * (bits m) 1 + (bits n) 5 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 1 * (bits n) 2 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 1 * (bits m) 0 * (bits m) 2 + (bits n) 2 * (bits m) 1 * (bits m) 2 + (bits n) 1 * (bits m) 3 + (bits n) 2 * (bits m) 3 + (bits n) 2 * (bits m) 4 + (bits n) 1 * (bits m) 5 + (bits n) 0 * (bits m) 6 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 0) && (bit n 2) && (bit m 1)) ^^ ((bit n 3) && (bit m 1)) ^^ ((bit n 5) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 1) && (bit n 2) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 1) && (bit m 0) && (bit m 2)) ^^ ((bit n 2) && (bit m 1) && (bit m 2)) ^^ ((bit n 1) && (bit m 3)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 2) && (bit m 4)) ^^ ((bit n 1) && (bit m 5)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_8 (n m : Fin 256) :
    obstruction 8 (bits n) (bits m) = fun k => zbit (bobstruction 8 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits m) 2 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 1 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 0 * (bits m) 1 + (bits n) 0 * (bits n) 1 * (bits m) 1 + (bits n) 2 * (bits m) 1 + (bits n) 4 * (bits m) 1 + (bits n) 5 * (bits m) 1 + (bits n) 1 * (bits m) 0 * (bits m) 1 + (bits n) 1 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 1 * (bits m) 4 + (bits n) 1 * (bits m) 5 + (bits n) 0 * (bits m) 6 = zbit (((bit n 1) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 0) && (bit m 1)) ^^ ((bit n 0) && (bit n 1) && (bit m 1)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 4) && (bit m 1)) ^^ ((bit n 5) && (bit m 1)) ^^ ((bit n 1) && (bit m 0) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 1) && (bit m 4)) ^^ ((bit n 1) && (bit m 5)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_9 (n m : Fin 256) :
    obstruction 9 (bits n) (bits m) = fun k => zbit (bobstruction 9 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 6 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 5 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 + (bits n) 0 * (bits n) 2 * (bits m) 2 + (bits n) 1 * (bits n) 2 * (bits m) 2 + (bits n) 4 * (bits m) 2 + (bits n) 2 * (bits m) 0 * (bits m) 2 + (bits n) 2 * (bits m) 1 * (bits m) 2 + (bits n) 2 * (bits m) 4 + (bits n) 1 * (bits m) 5 + (bits n) 0 * (bits m) 6 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 6) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 5) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)) ^^ ((bit n 0) && (bit n 2) && (bit m 2)) ^^ ((bit n 1) && (bit n 2) && (bit m 2)) ^^ ((bit n 4) && (bit m 2)) ^^ ((bit n 2) && (bit m 0) && (bit m 2)) ^^ ((bit n 2) && (bit m 1) && (bit m 2)) ^^ ((bit n 2) && (bit m 4)) ^^ ((bit n 1) && (bit m 5)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool_10 (n m : Fin 256) :
    obstruction 10 (bits n) (bits m) = fun k => zbit (bobstruction 10 n m k) := by
  funext k; fin_cases k
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change 0 = zbit (false)
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 0 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 0) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 0 * (bits m) 2 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 0) && (bit m 2)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 2 * (bits m) 1 + (bits n) 1 * (bits m) 2 = zbit (((bit n 2) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]
  · change (bits n) 6 * (bits m) 0 + (bits n) 2 * (bits m) 1 + (bits n) 5 * (bits m) 1 + (bits n) 2 * (bits m) 0 * (bits m) 1 + (bits n) 1 * (bits m) 2 + (bits n) 0 * (bits n) 1 * (bits m) 2 + (bits n) 3 * (bits m) 2 + (bits n) 2 * (bits m) 3 + (bits n) 1 * (bits m) 5 + (bits n) 0 * (bits m) 6 = zbit (((bit n 6) && (bit m 0)) ^^ ((bit n 2) && (bit m 1)) ^^ ((bit n 5) && (bit m 1)) ^^ ((bit n 2) && (bit m 0) && (bit m 1)) ^^ ((bit n 1) && (bit m 2)) ^^ ((bit n 0) && (bit n 1) && (bit m 2)) ^^ ((bit n 3) && (bit m 2)) ^^ ((bit n 2) && (bit m 3)) ^^ ((bit n 1) && (bit m 5)) ^^ ((bit n 0) && (bit m 6)))
    simp only [bits_bit, zbit_xor, zbit_and, show zbit false = 0 from rfl]

public theorem obstruction_bool (i : Fin 11) (n m : Fin 256) :
    obstruction i (bits n) (bits m) = fun k => zbit (bobstruction i n m k) := by
  fin_cases i
  · exact obstruction_bool_0 n m
  · exact obstruction_bool_1 n m
  · exact obstruction_bool_2 n m
  · exact obstruction_bool_3 n m
  · exact obstruction_bool_4 n m
  · exact obstruction_bool_5 n m
  · exact obstruction_bool_6 n m
  · exact obstruction_bool_7 n m
  · exact obstruction_bool_8 n m
  · exact obstruction_bool_9 n m
  · exact obstruction_bool_10 n m

@[expose] public def bcomm (i : Fin 11) (n m : Fin 256) : Prop :=
  ∀ k, bobstruction i n m k = false
public instance (i : Fin 11) (n m : Fin 256) : Decidable (bcomm i n m) := by
  unfold bcomm; infer_instance

public theorem comm_bool (i : Fin 11) (n m : Fin 256) :
    comm i (bits n) (bits m) ↔ bcomm i n m := by
  rw [comm_obstruction, obstruction_bool]
  simp only [zbit_zero, bcomm]

@[expose] public def bcent (i : Fin 11) (n : Fin 256) : ℕ :=
  (Finset.univ.filter (fun m : Fin 256 => bcomm i m n)).card

public theorem cent_bool (i : Fin 11) (n : Fin 256) : cent i (bits n) = bcent i n := by
  unfold cent bcent
  congr 1
  apply Finset.filter_congr
  intro m _
  exact comm_bool i m n

@[expose] public def centTable (i : Fin 11) (w : A256Bits) : ℕ :=
  ((![([256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32] : List ℕ),
([256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32] : List ℕ),
([256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32] : List ℕ),
([256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32] : List ℕ),
([256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32] : List ℕ),
([256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64] : List ℕ),
([256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32] : List ℕ),
([256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64] : List ℕ),
([256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32] : List ℕ),
([256, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64] : List ℕ),
([256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32] : List ℕ)]) i).getD (number w).val 0

public abbrev B8 := Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool
@[expose] public def tupleBit (w : B8) : Fin 8 → Bool :=
  ![w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2.1,w.2.2.2.2.2.2.1,w.2.2.2.2.2.2.2]

@[expose] public def tupleNumber (w : B8) : Fin 256 :=
  Fin.ofNat 256 (w.1.toNat + 2*w.2.1.toNat + 4*w.2.2.1.toNat + 8*w.2.2.2.1.toNat +
    16*w.2.2.2.2.1.toNat + 32*w.2.2.2.2.2.1.toNat + 64*w.2.2.2.2.2.2.1.toNat +
    128*w.2.2.2.2.2.2.2.toNat)
@[expose] public def numberTuple (n : Fin 256) : B8 :=
  (bit n 0,bit n 1,bit n 2,bit n 3,bit n 4,bit n 5,bit n 6,bit n 7)
@[expose] public def tupleEquiv : B8 ≃ Fin 256 where
  toFun := tupleNumber
  invFun := numberTuple
  left_inv := by decide +kernel
  right_inv := by decide +kernel
public theorem tupleNumber_bit : ∀ w k, bit (tupleNumber w) k = tupleBit w k := by
  decide +kernel
@[expose] public def quickComm (i : Fin 11) (w z : B8) : Bool :=
  match i.val with
  | 0 => !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 1 => !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 2 => !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 3 => !((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 4 => !((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 5 => !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))
  | 6 => !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))
  | 7 => !((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 8 => !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | 9 => !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))
  | _ => !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))

public theorem forall10 (f : Fin 10 → Bool) : (∀ k, f k = false) ↔
    f 0 = false ∧ f 1 = false ∧ f 2 = false ∧ f 3 = false ∧ f 4 = false ∧
    f 5 = false ∧ f 6 = false ∧ f 7 = false ∧ f 8 = false ∧ f 9 = false := by
  simp [Fin.forall_fin_succ]

public theorem bcomm_quick (i : Fin 11) (w z : B8) :
    bcomm i (tupleNumber w) (tupleNumber z) ↔ quickComm i w z = true := by
  unfold bcomm
  rw [forall10]
  fin_cases i
  · change ((false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 4) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber w) 4) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ True ∧ True ∧ ((w.2.1 && w.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && w.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.1 && z.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.1 && z.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.1 && w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 5))) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1)) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 3))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 4))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 3) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 5))) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1)) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.1 && z.2.2.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.1 && z.1) ^^ (w.1 && w.2.2.2.1 && z.1) ^^ (w.2.2.2.2.2.1 && z.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.1 && z.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 5)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.1 && w.2.2.1 && z.2.1) ^^ (w.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 5)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ True ∧ ((w.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.1 && z.1) ^^ (w.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.1 && z.2.1) ^^ (w.1 && w.2.1 && z.2.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber w) 2) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 4) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 4)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 5)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ True ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.1 && w.2.2.1 && z.2.2.1) ^^ (w.2.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]
  · change ((false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (false) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2))) = false ∧ (((bit (tupleNumber w) 6) && (bit (tupleNumber z) 0)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 5) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 0) && (bit (tupleNumber z) 1)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber w) 1) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 3) && (bit (tupleNumber z) 2)) ^^ ((bit (tupleNumber w) 2) && (bit (tupleNumber z) 3)) ^^ ((bit (tupleNumber w) 1) && (bit (tupleNumber z) 5)) ^^ ((bit (tupleNumber w) 0) && (bit (tupleNumber z) 6))) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [tupleNumber_bit]
    change (True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ ((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) = false ∧ ((w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1)) = false) ↔ (!((w.2.2.1 && z.1) ^^ (w.1 && z.2.2.1)) && !((w.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.1 && z.2.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.1 && z.2.1) ^^ (w.2.1 && z.2.2.1)) && !((w.2.2.2.2.2.2.1 && z.1) ^^ (w.2.2.1 && z.2.1) ^^ (w.2.2.2.2.2.1 && z.2.1) ^^ (w.2.2.1 && z.1 && z.2.1) ^^ (w.2.1 && z.2.2.1) ^^ (w.1 && w.2.1 && z.2.2.1) ^^ (w.2.2.2.1 && z.2.2.1) ^^ (w.2.2.1 && z.2.2.2.1) ^^ (w.2.1 && z.2.2.2.2.2.1) ^^ (w.1 && z.2.2.2.2.2.2.1))) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_true,
      true_and, and_self, and_assoc, and_self_left]

@[expose] public def allB8 : List B8 := [(false,false,false,false,false,false,false,false),(true,false,false,false,false,false,false,false),(false,true,false,false,false,false,false,false),(true,true,false,false,false,false,false,false),(false,false,true,false,false,false,false,false),(true,false,true,false,false,false,false,false),(false,true,true,false,false,false,false,false),(true,true,true,false,false,false,false,false),(false,false,false,true,false,false,false,false),(true,false,false,true,false,false,false,false),(false,true,false,true,false,false,false,false),(true,true,false,true,false,false,false,false),(false,false,true,true,false,false,false,false),(true,false,true,true,false,false,false,false),(false,true,true,true,false,false,false,false),(true,true,true,true,false,false,false,false),(false,false,false,false,true,false,false,false),(true,false,false,false,true,false,false,false),(false,true,false,false,true,false,false,false),(true,true,false,false,true,false,false,false),(false,false,true,false,true,false,false,false),(true,false,true,false,true,false,false,false),(false,true,true,false,true,false,false,false),(true,true,true,false,true,false,false,false),(false,false,false,true,true,false,false,false),(true,false,false,true,true,false,false,false),(false,true,false,true,true,false,false,false),(true,true,false,true,true,false,false,false),(false,false,true,true,true,false,false,false),(true,false,true,true,true,false,false,false),(false,true,true,true,true,false,false,false),(true,true,true,true,true,false,false,false),(false,false,false,false,false,true,false,false),(true,false,false,false,false,true,false,false),(false,true,false,false,false,true,false,false),(true,true,false,false,false,true,false,false),(false,false,true,false,false,true,false,false),(true,false,true,false,false,true,false,false),(false,true,true,false,false,true,false,false),(true,true,true,false,false,true,false,false),(false,false,false,true,false,true,false,false),(true,false,false,true,false,true,false,false),(false,true,false,true,false,true,false,false),(true,true,false,true,false,true,false,false),(false,false,true,true,false,true,false,false),(true,false,true,true,false,true,false,false),(false,true,true,true,false,true,false,false),(true,true,true,true,false,true,false,false),(false,false,false,false,true,true,false,false),(true,false,false,false,true,true,false,false),(false,true,false,false,true,true,false,false),(true,true,false,false,true,true,false,false),(false,false,true,false,true,true,false,false),(true,false,true,false,true,true,false,false),(false,true,true,false,true,true,false,false),(true,true,true,false,true,true,false,false),(false,false,false,true,true,true,false,false),(true,false,false,true,true,true,false,false),(false,true,false,true,true,true,false,false),(true,true,false,true,true,true,false,false),(false,false,true,true,true,true,false,false),(true,false,true,true,true,true,false,false),(false,true,true,true,true,true,false,false),(true,true,true,true,true,true,false,false),(false,false,false,false,false,false,true,false),(true,false,false,false,false,false,true,false),(false,true,false,false,false,false,true,false),(true,true,false,false,false,false,true,false),(false,false,true,false,false,false,true,false),(true,false,true,false,false,false,true,false),(false,true,true,false,false,false,true,false),(true,true,true,false,false,false,true,false),(false,false,false,true,false,false,true,false),(true,false,false,true,false,false,true,false),(false,true,false,true,false,false,true,false),(true,true,false,true,false,false,true,false),(false,false,true,true,false,false,true,false),(true,false,true,true,false,false,true,false),(false,true,true,true,false,false,true,false),(true,true,true,true,false,false,true,false),(false,false,false,false,true,false,true,false),(true,false,false,false,true,false,true,false),(false,true,false,false,true,false,true,false),(true,true,false,false,true,false,true,false),(false,false,true,false,true,false,true,false),(true,false,true,false,true,false,true,false),(false,true,true,false,true,false,true,false),(true,true,true,false,true,false,true,false),(false,false,false,true,true,false,true,false),(true,false,false,true,true,false,true,false),(false,true,false,true,true,false,true,false),(true,true,false,true,true,false,true,false),(false,false,true,true,true,false,true,false),(true,false,true,true,true,false,true,false),(false,true,true,true,true,false,true,false),(true,true,true,true,true,false,true,false),(false,false,false,false,false,true,true,false),(true,false,false,false,false,true,true,false),(false,true,false,false,false,true,true,false),(true,true,false,false,false,true,true,false),(false,false,true,false,false,true,true,false),(true,false,true,false,false,true,true,false),(false,true,true,false,false,true,true,false),(true,true,true,false,false,true,true,false),(false,false,false,true,false,true,true,false),(true,false,false,true,false,true,true,false),(false,true,false,true,false,true,true,false),(true,true,false,true,false,true,true,false),(false,false,true,true,false,true,true,false),(true,false,true,true,false,true,true,false),(false,true,true,true,false,true,true,false),(true,true,true,true,false,true,true,false),(false,false,false,false,true,true,true,false),(true,false,false,false,true,true,true,false),(false,true,false,false,true,true,true,false),(true,true,false,false,true,true,true,false),(false,false,true,false,true,true,true,false),(true,false,true,false,true,true,true,false),(false,true,true,false,true,true,true,false),(true,true,true,false,true,true,true,false),(false,false,false,true,true,true,true,false),(true,false,false,true,true,true,true,false),(false,true,false,true,true,true,true,false),(true,true,false,true,true,true,true,false),(false,false,true,true,true,true,true,false),(true,false,true,true,true,true,true,false),(false,true,true,true,true,true,true,false),(true,true,true,true,true,true,true,false),(false,false,false,false,false,false,false,true),(true,false,false,false,false,false,false,true),(false,true,false,false,false,false,false,true),(true,true,false,false,false,false,false,true),(false,false,true,false,false,false,false,true),(true,false,true,false,false,false,false,true),(false,true,true,false,false,false,false,true),(true,true,true,false,false,false,false,true),(false,false,false,true,false,false,false,true),(true,false,false,true,false,false,false,true),(false,true,false,true,false,false,false,true),(true,true,false,true,false,false,false,true),(false,false,true,true,false,false,false,true),(true,false,true,true,false,false,false,true),(false,true,true,true,false,false,false,true),(true,true,true,true,false,false,false,true),(false,false,false,false,true,false,false,true),(true,false,false,false,true,false,false,true),(false,true,false,false,true,false,false,true),(true,true,false,false,true,false,false,true),(false,false,true,false,true,false,false,true),(true,false,true,false,true,false,false,true),(false,true,true,false,true,false,false,true),(true,true,true,false,true,false,false,true),(false,false,false,true,true,false,false,true),(true,false,false,true,true,false,false,true),(false,true,false,true,true,false,false,true),(true,true,false,true,true,false,false,true),(false,false,true,true,true,false,false,true),(true,false,true,true,true,false,false,true),(false,true,true,true,true,false,false,true),(true,true,true,true,true,false,false,true),(false,false,false,false,false,true,false,true),(true,false,false,false,false,true,false,true),(false,true,false,false,false,true,false,true),(true,true,false,false,false,true,false,true),(false,false,true,false,false,true,false,true),(true,false,true,false,false,true,false,true),(false,true,true,false,false,true,false,true),(true,true,true,false,false,true,false,true),(false,false,false,true,false,true,false,true),(true,false,false,true,false,true,false,true),(false,true,false,true,false,true,false,true),(true,true,false,true,false,true,false,true),(false,false,true,true,false,true,false,true),(true,false,true,true,false,true,false,true),(false,true,true,true,false,true,false,true),(true,true,true,true,false,true,false,true),(false,false,false,false,true,true,false,true),(true,false,false,false,true,true,false,true),(false,true,false,false,true,true,false,true),(true,true,false,false,true,true,false,true),(false,false,true,false,true,true,false,true),(true,false,true,false,true,true,false,true),(false,true,true,false,true,true,false,true),(true,true,true,false,true,true,false,true),(false,false,false,true,true,true,false,true),(true,false,false,true,true,true,false,true),(false,true,false,true,true,true,false,true),(true,true,false,true,true,true,false,true),(false,false,true,true,true,true,false,true),(true,false,true,true,true,true,false,true),(false,true,true,true,true,true,false,true),(true,true,true,true,true,true,false,true),(false,false,false,false,false,false,true,true),(true,false,false,false,false,false,true,true),(false,true,false,false,false,false,true,true),(true,true,false,false,false,false,true,true),(false,false,true,false,false,false,true,true),(true,false,true,false,false,false,true,true),(false,true,true,false,false,false,true,true),(true,true,true,false,false,false,true,true),(false,false,false,true,false,false,true,true),(true,false,false,true,false,false,true,true),(false,true,false,true,false,false,true,true),(true,true,false,true,false,false,true,true),(false,false,true,true,false,false,true,true),(true,false,true,true,false,false,true,true),(false,true,true,true,false,false,true,true),(true,true,true,true,false,false,true,true),(false,false,false,false,true,false,true,true),(true,false,false,false,true,false,true,true),(false,true,false,false,true,false,true,true),(true,true,false,false,true,false,true,true),(false,false,true,false,true,false,true,true),(true,false,true,false,true,false,true,true),(false,true,true,false,true,false,true,true),(true,true,true,false,true,false,true,true),(false,false,false,true,true,false,true,true),(true,false,false,true,true,false,true,true),(false,true,false,true,true,false,true,true),(true,true,false,true,true,false,true,true),(false,false,true,true,true,false,true,true),(true,false,true,true,true,false,true,true),(false,true,true,true,true,false,true,true),(true,true,true,true,true,false,true,true),(false,false,false,false,false,true,true,true),(true,false,false,false,false,true,true,true),(false,true,false,false,false,true,true,true),(true,true,false,false,false,true,true,true),(false,false,true,false,false,true,true,true),(true,false,true,false,false,true,true,true),(false,true,true,false,false,true,true,true),(true,true,true,false,false,true,true,true),(false,false,false,true,false,true,true,true),(true,false,false,true,false,true,true,true),(false,true,false,true,false,true,true,true),(true,true,false,true,false,true,true,true),(false,false,true,true,false,true,true,true),(true,false,true,true,false,true,true,true),(false,true,true,true,false,true,true,true),(true,true,true,true,false,true,true,true),(false,false,false,false,true,true,true,true),(true,false,false,false,true,true,true,true),(false,true,false,false,true,true,true,true),(true,true,false,false,true,true,true,true),(false,false,true,false,true,true,true,true),(true,false,true,false,true,true,true,true),(false,true,true,false,true,true,true,true),(true,true,true,false,true,true,true,true),(false,false,false,true,true,true,true,true),(true,false,false,true,true,true,true,true),(false,true,false,true,true,true,true,true),(true,true,false,true,true,true,true,true),(false,false,true,true,true,true,true,true),(true,false,true,true,true,true,true,true),(false,true,true,true,true,true,true,true),(true,true,true,true,true,true,true,true)]


public theorem allB8_nodup : allB8.Nodup := by decide +kernel
public theorem allB8_univ : allB8.toFinset = Finset.univ := by decide +kernel
@[expose] public def quickCent (i : Fin 11) (w : B8) : ℕ :=
  allB8.countP (fun z => quickComm i z w)

public theorem bcent_quick (i : Fin 11) (w : B8) :
    bcent i (tupleNumber w) = quickCent i w := by
  have h : Fintype.card {n : Fin 256 // bcomm i n (tupleNumber w)} =
      Fintype.card {z : B8 // quickComm i z w = true} := by
    apply Fintype.card_congr
    exact (tupleEquiv.subtypeEquiv (fun z => (bcomm_quick i z w).symm)).symm
  simp only [Fintype.card_subtype] at h
  change _ = _ at h
  rw [bcent, h, ← allB8_univ, allB8_nodup.card_eq_countP]
  simp only [Bool.decide_coe, quickCent]


end ReeTwo.SylowModel.A256Count
