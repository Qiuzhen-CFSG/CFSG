module

public import Theory.GroupAction.FiveFourBinaryCoordinates

/-!
# An isotropic square for the five-four action

The square map of a class-three group has an identity relating its polarization
to the central commutator pairing. For the paired four-dimensional binary
five-four representations this identity forces a nonidentity zero. Compatible
coordinates are obtained using an auxiliary constant square map; the actual
square is never assumed to have a nonidentity zero.
-/

namespace Theory.GroupAction.FiveFourBinaryModel

private def seedVec (n : Fin 16) : Space :=
  Multiplicative.ofAdd fun i => if (BitVec.ofFin n).getLsb i then 1 else 0

private def seedTable (a b : Space) : Fin 16 → Space :=
  ![1, b, translate (turn b), translate b, translate^[4] (turn b),
    translate^[2] (turn b), translate^[2] b, a, translate^[4] b, turn b,
    translate^[3] (turn b), translate^[4] a, translate^[3] b,
    translate^[3] a, translate^[2] a, translate a]

private theorem seedTable_identity : ∀ n, seedTable (seedVec 7) (seedVec 1) n = seedVec n :=
  by decide +kernel

private theorem seedTable_natural (q : Space → Space) (h1 : q 1 = 1)
    (ht : ∀ x, q (translate x) = translate (q x))
    (hs : ∀ x, q (turn x) = turn (q x)) (n : Fin 16) :
    q (seedTable (seedVec 7) (seedVec 1) n) =
      seedTable (q (seedVec 7)) (q (seedVec 1)) n := by
  fin_cases n <;> simp [seedTable, h1, ht, hs]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
private theorem seed_candidates : ∀ a b : Space,
    turn a = translate^[3] a →
    (∀ n, pairing (seedVec n) (seedTable a b n) = 1) →
    (seedTable a b 7 * seedTable a b 3 * seedTable a b 5 * seedTable a b 6 *
      seedTable a b 1 * seedTable a b 2 * seedTable a b 4 = 1) →
    pairing (seedVec 2) (seedTable a b 1) =
      pairing (seedVec 1) (seedTable a b 3 * seedTable a b 1 * seedTable a b 2) →
    a = 1 := by decide +kernel

/-- A binary five-four equivariant square satisfying the square-commutator
identity has a nonidentity zero. -/
public theorem square_has_nontrivial_zero_of_commutator_identity
    (q : Space → Space) (h1 : q 1 = 1)
    (ht : ∀ x, q (translate x) = translate (q x))
    (hs : ∀ x, q (turn x) = turn (q x))
    (hq : ∀ a b c, q (a * b * c) * q (a * b) * q (a * c) *
      q (b * c) * q a * q b * q c = 1)
    (hself : ∀ x, pairing x (q x) = 1)
    (hc : ∀ x y, pairing y (q x) = pairing x (q (x * y) * q x * q y)) :
    ∃ x, x ≠ 1 ∧ q x = 1 := by
  have htable (n) : seedTable (q (seedVec 7)) (q (seedVec 1)) n = q (seedVec n) := by
    rw [← seedTable_identity n]
    exact (seedTable_natural q h1 ht hs n).symm
  have ht7 : turn (q (seedVec 7)) = translate^[3] (q (seedVec 7)) := by
    rw [← hs]
    have hh : turn (seedVec 7) = seedVec 13 := by decide +kernel
    rw [hh, ← htable]
    rfl
  have h12 : seedVec 1 * seedVec 2 = seedVec 3 := by decide +kernel
  have h14 : seedVec 1 * seedVec 4 = seedVec 5 := by decide +kernel
  have h24 : seedVec 2 * seedVec 4 = seedVec 6 := by decide +kernel
  have h34 : seedVec 3 * seedVec 4 = seedVec 7 := by decide +kernel
  refine ⟨seedVec 7, by decide +kernel, ?_⟩
  apply seed_candidates (q (seedVec 7)) (q (seedVec 1)) ht7
  · intro n
    rw [htable]
    exact hself _
  · simp only [htable]
    simpa only [h12, h14, h24, h34] using hq (seedVec 1) (seedVec 2) (seedVec 4)
  · simp only [htable]
    simpa only [h12] using hc (seedVec 1) (seedVec 2)

end Theory.GroupAction.FiveFourBinaryModel

namespace Theory.GroupAction
open FiveFourBinaryModel
open scoped IsMulCommutative

/-- The square-commutator identity supplies the isotropic vector for any
faithful paired binary five-four action on groups of order sixteen. -/
public theorem five_four_square_has_nontrivial_zero
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (leftAction : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut V)
    (rightAction : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut W)
    (hl : Function.Injective leftAction) (hr : Function.Injective rightAction)
    (p : V →* (W →* Multiplicative (ZMod 2))) (hp : Function.Injective p)
    (hequiv : ∀ a v w, p (leftAction a v) (rightAction a w) = p v w)
    (q : V → W) (h1 : q 1 = 1)
    (hq : ∀ a b c, q (a * b * c) * q (a * b) * q (a * c) *
      q (b * c) * q a * q b * q c = 1)
    (hself : ∀ x, p x (q x) = 1)
    (hqequiv : ∀ a v, q (leftAction a v) = rightAction a (q v))
    (hc : ∀ x y, p y (q x) = p x (q (x * y) * q x * q y)) :
    ∃ x, x ≠ 1 ∧ q x = 1 := by
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  let d : BinaryQuadraticPairing
      (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) V W := {
    pairing := p
    pairing_injective := hp
    square := fun _ => 1
    square_one := rfl
    square_quadratic := by intros; simp
    square_self := by intro x; exact map_one (p x)
    square_has_nontrivial_zero := ⟨v, hv, rfl⟩
    leftAction := leftAction
    rightAction := rightAction
    leftAction_injective := hl
    rightAction_injective := hr
    pairing_equivariant := hequiv
    square_equivariant := by intro a x; exact (map_one (rightAction a)).symm }
  let g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4) :=
    SemidirectProduct.inr (Multiplicative.ofAdd 1)
  have hg : orderOf g = 4 := by
    rw [orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
    simp [orderOf_ofAdd_eq_addOrderOf]
  obtain ⟨c⟩ := d.exists_five_four_coordinates hV hW φ hφ g hg
  let q' : Space → Space := fun x => c.right (q (c.left.symm x))
  have hqt (x : Space) : q' (translate x) = translate (q' x) := by
    have hx : c.left.symm (translate x) = leftAction c.translationActor (c.left.symm x) := by
      apply c.left.injective
      change c.left (c.left.symm (translate x)) =
        c.left (d.leftAction c.translationActor (c.left.symm x))
      rw [c.left_translate, c.left.apply_symm_apply, c.left.apply_symm_apply]
    dsimp [q']
    rw [hx, hqequiv]
    exact c.right_translate _
  have hqs (x : Space) : q' (turn x) = turn (q' x) := by
    have hx : c.left.symm (turn x) = leftAction c.turnActor (c.left.symm x) := by
      apply c.left.injective
      change c.left (c.left.symm (turn x)) =
        c.left (d.leftAction c.turnActor (c.left.symm x))
      rw [c.left_turn, c.left.apply_symm_apply, c.left.apply_symm_apply]
    dsimp [q']
    rw [hx, hqequiv]
    exact c.right_turn _
  have hq1 : q' 1 = 1 := by simp [q', h1]
  have hqq (x y z : Space) : q' (x * y * z) * q' (x * y) * q' (x * z) *
      q' (y * z) * q' x * q' y * q' z = 1 := by
    simpa only [q', map_mul, map_one] using
      congrArg c.right (hq (c.left.symm x) (c.left.symm y) (c.left.symm z))
  have hself' (x : Space) : pairing x (q' x) = 1 := by
    have hh := hself (c.left.symm x)
    change d.pairing _ _ = 1 at hh
    rw [c.pairing_eq, c.left.apply_symm_apply] at hh
    exact hh
  have hc' (x y : Space) : pairing y (q' x) =
      pairing x (q' (x * y) * q' x * q' y) := by
    have hh := hc (c.left.symm x) (c.left.symm y)
    change d.pairing _ _ = d.pairing _ _ at hh
    simpa only [q', c.pairing_eq, c.left.apply_symm_apply, map_mul] using hh
  obtain ⟨x, hx, hqx⟩ := square_has_nontrivial_zero_of_commutator_identity q'
    hq1 hqt hqs hqq hself' hc'
  refine ⟨c.left.symm x, ?_, ?_⟩
  · intro hh
    exact hx (c.left.symm.injective (hh.trans (map_one c.left.symm).symm))
  · exact c.right.injective (hqx.trans (map_one c.right).symm)

end Theory.GroupAction
