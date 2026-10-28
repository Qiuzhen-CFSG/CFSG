module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates

/-!
# Intrinsic fiber counts for the first four small parity candidates

Nine binary parameters enumerate each proposed carrier in rows 0–3. Checking
root powers identifies the restricted complement action, and symbolic
collection gives its multiplication formula. The last two binary parameters
cancel from commutation, so centralizer orders are four times counts over
128 reduced tuples. Boolean coordinates, proved equivalent to field arithmetic,
keep the kernel calculations small. Finite calculations certify these orders
and the three prescribed tests in every fiber of the fixed coordinate map.

All centralizers are taken inside the candidate. The only identification
assumed is equality of the proposed carrier with the original generator
closure; neither multiplicativity of the coordinate map nor a Frattini-kernel
certificate is used.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified multiplication
in `Core`, `RootAction`, and `Sylow`. The row and basis conventions are those
of `SmallParityProfiles` and `SmallParityFourCoordinates`.
-/

namespace ReeTwo.SylowModel

set_option maxRecDepth 16384
set_option synthInstance.maxSize 8192

private abbrev Bits7 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private abbrev Params := ZMod 4 × Bits7

private def elt (i : Fin 4) (w : Params) : SylowModel :=
  let t := w.1
  let a := w.2.1
  let b := w.2.2.1
  let c := w.2.2.2.1
  let d := w.2.2.2.2.1
  let e := w.2.2.2.2.2.1
  let f := w.2.2.2.2.2.2.1
  let g := w.2.2.2.2.2.2.2
  ⟨(![⟨0, 0, a, b, c, 0, d, e, f, g⟩,
      ⟨0, 0, a, b, c, (t.val : ZMod 2), d, e, f, g⟩,
      ⟨0, 0, a, 0, b, c, d, e, f, g⟩,
      ⟨0, 0, a, c, b, c, d, e, f, g⟩] : Fin 4 → Core) i,
    Multiplicative.ofAdd t⟩

private def read (i : Fin 4) (x : SylowModel) : Params :=
  (x.right.toAdd, x.left.b2, if i.val < 2 then x.left.b3 else x.left.b4,
    if i.val < 2 then x.left.b4 else x.left.b5,
    x.left.b6, x.left.b7, x.left.b8, x.left.b9)

private theorem read_elt : ∀ i w, read i (elt i w) = w := by
  intro i w
  fin_cases i <;> rfl

private theorem elt_carrier : ∀ i w, smallParityFourCarrier ⟨i.val, by omega⟩ (elt i w) := by
  intro i w
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem elt_read : ∀ (i : Fin 4) (x : SylowModel),
    smallParityFourCarrier ⟨i.val, by omega⟩ x → elt i (read i x) = x := by
  rintro i ⟨⟨a,b,c,d,e,f,g,h,j,k⟩,t⟩ hx
  fin_cases i <;> dsimp [smallParityFourCarrier] at hx
  all_goals rcases hx with ⟨rfl, rfl, rfl⟩
  all_goals rfl

-- The restricted complement action is linear in the eight core coordinates.
private def act (t : ZMod 4) (x : Core) : Core :=
  let u : ZMod 2 := t.val
  let v : ZMod 2 := (t.val / 2 : ℕ)
  ⟨0, 0, x.b2, x.b3, x.b4 + u * x.b3, x.b5,
    x.b6 + u * x.b5,
    x.b7 + u * x.b6 + v * x.b5,
    x.b8 + u * (x.b5 + x.b6 + x.b7) + v * (x.b5 + x.b6) + u * v * x.b5,
    x.b9 + u * (x.b5 + x.b6) + v * x.b5⟩

private def eight (w : ZMod 2 × Bits7) : Core :=
  ⟨0, 0, w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1,
    w.2.2.2.2.2.1, w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2⟩

private theorem act_root_pow : ∀ (t : ZMod 4) (i : Fin 8) (z : ZMod 2),
    Core.complementAction (SemidirectProduct.inr (Multiplicative.ofAdd t))
      (Core.root ⟨i.val + 2, by omega⟩ ^ z.val) =
      act t (Core.root ⟨i.val + 2, by omega⟩ ^ z.val) := by decide +kernel

private theorem core_mul_def (a b : Core) : a * b = Core.mul a b := rfl

private theorem act_eq (t : ZMod 4) (w : ZMod 2 × Bits7) :
    Core.complementAction (SemidirectProduct.inr (Multiplicative.ofAdd t)) (eight w) =
      act t (eight w) := by
  conv_lhs => rw [← Core.normal_form (eight w)]
  simp only [eight, ZMod.val_zero, pow_zero, one_mul, map_mul]
  erw [act_root_pow t 0 w.1, act_root_pow t 1 w.2.1, act_root_pow t 2 w.2.2.1,
    act_root_pow t 3 w.2.2.2.1, act_root_pow t 4 w.2.2.2.2.1,
    act_root_pow t 5 w.2.2.2.2.2.1, act_root_pow t 6 w.2.2.2.2.2.2.1,
    act_root_pow t 7 w.2.2.2.2.2.2.2]
  simp only [Core.root_pow]
  apply Core.ext <;>
    simp [act, Core.ofCoords, core_mul_def, Core.mul] <;> ring

private def fastMul (x y : SylowModel) : SylowModel :=
  let u : ZMod 2 := x.right.toAdd.val
  let v : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  let a := x.left
  let b := y.left
  ⟨⟨0, 0, a.b2 + b.b2, a.b3 + b.b3, a.b4 + b.b4 + u * b.b3,
    a.b5 + b.b5, a.b6 + b.b6 + u * b.b5,
    a.b7 + b.b7 + u * b.b6 + v * b.b5 + a.b3 * b.b2,
    a.b8 + b.b8 + u * (b.b5 + b.b6 + b.b7) + v * (b.b5 + b.b6) +
      u * v * b.b5 + a.b4 * b.b2 + a.b3 * b.b3,
    a.b9 + b.b9 + u * (b.b5 + b.b6) + v * b.b5 + a.b2 * b.b2 +
      a.b6 * b.b3 + a.b5 * (b.b4 + u * b.b3)⟩,
    x.right * y.right⟩

private theorem mul_eq (x y : SylowModel)
    (hx0 : x.left.b0 = 0) (hx1 : x.left.b1 = 0)
    (hy0 : y.left.b0 = 0) (hy1 : y.left.b1 = 0) : x * y = fastMul x y := by
  have hy : y.left = eight (y.left.b2, y.left.b3, y.left.b4, y.left.b5,
      y.left.b6, y.left.b7, y.left.b8, y.left.b9) := by
    apply Core.ext <;> simp [eight, hy0, hy1]
  apply SemidirectProduct.ext
  · change Core.mul x.left (Core.complementAction (SemidirectProduct.inr x.right) y.left) = _
    rw [hy]
    erw [act_eq x.right.toAdd (y.left.b2, y.left.b3, y.left.b4, y.left.b5,
      y.left.b6, y.left.b7, y.left.b8, y.left.b9)]
    apply Core.ext <;> simp [Core.mul, act, eight, fastMul, hx0, hx1] <;> ring
  · rfl

private def paramEquiv (i : Fin 4)
    (hc : ∀ x, x ∈ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) ↔
      smallParityFourCarrier ⟨i.val, by omega⟩ x) :
    Params ≃ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) where
  toFun w := ⟨elt i w, (hc _).mpr (elt_carrier i w)⟩
  invFun x := read i x
  left_inv := read_elt i
  right_inv x := Subtype.ext (elt_read i x ((hc x).mp x.property))

private def cent (i : Fin 4) (x : SylowModel) : ℕ :=
  Fintype.card {w : Params // fastMul (elt i w) x = fastMul x (elt i w)}

private theorem cent_eq (i : Fin 4)
    (hc : ∀ x, x ∈ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) ↔
      smallParityFourCarrier ⟨i.val, by omega⟩ x)
    (x : smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩)) :
    MulAut.commutingCard x = cent i x := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (paramEquiv i hc)]
  simp only [cent, Fintype.card_subtype]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Subtype.coe_inj]
  change elt i w * x.val = x.val * elt i w ↔ _
  have hx := (hc x).mp x.property
  have hw := elt_carrier i w
  rw [mul_eq _ _ hw.1 hw.2.1 hx.1 hx.2.1,
    mul_eq _ _ hx.1 hx.2.1 hw.1 hw.2.1]

private def fastOrder (n : ℕ) (x : SylowModel) : Prop :=
  if n = 1 then x = 1 else if n = 2 then fastMul x x = 1 ∧ x ≠ 1
  else n = 4 ∧ fastMul (fastMul x x) (fastMul x x) = 1 ∧ fastMul x x ≠ 1

private instance (n : ℕ) (x : SylowModel) : Decidable (fastOrder n x) := by
  unfold fastOrder
  infer_instance

private theorem order_four_iff {G : Type*} [Group G] (x : G) :
    orderOf x = 4 ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    refine ⟨by simpa [h] using pow_orderOf_eq_one x, ?_⟩
    intro h2
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [h] at hd
    norm_num at hd
  · rintro ⟨h4, h2⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4

private theorem fastOrder_eq (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (x : SylowModel) (h0 : x.left.b0 = 0) (h1 : x.left.b1 = 0) :
    orderOf x = n ↔ fastOrder n x := by
  have hs : x ^ 2 = fastMul x x := by rw [pow_two, mul_eq x x h0 h1 h0 h1]
  have hf : x ^ 4 = fastMul (fastMul x x) (fastMul x x) := by
    change x ^ (2 * 2) = _
    rw [pow_mul, hs, pow_two,
      mul_eq _ _ rfl rfl rfl rfl]
  rcases hn with rfl | rfl | rfl
  · simp [fastOrder, orderOf_eq_one_iff]
  · simp [fastOrder, orderOf_eq_prime_iff, hs]
  · simp [fastOrder, order_four_iff, hs, hf]

private def test (i : Fin 4) (j : Fin 3) (x : SylowModel) : Prop :=
  let t := smallParityFourTests ⟨i.val, by omega⟩ j
  fastOrder t.1 x ∧ cent i x = t.2.1

private instance (i : Fin 4) (j : Fin 3) (x : SylowModel) : Decidable (test i j x) := by
  unfold test
  infer_instance

private theorem test_eq (i : Fin 4) (j : Fin 3)
    (hc : ∀ x, x ∈ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) ↔
      smallParityFourCarrier ⟨i.val, by omega⟩ x)
    (x : smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩)) :
    MulAut.orderCentralizerTest (smallParityFourTests ⟨i.val, by omega⟩ j) x ↔
      test i j x := by
  have ht : (smallParityFourTests ⟨i.val, by omega⟩ j).2.2 = 0 := by
    fin_cases i <;> fin_cases j <;> rfl
  have ho : (smallParityFourTests ⟨i.val, by omega⟩ j).1 = 1 ∨
      (smallParityFourTests ⟨i.val, by omega⟩ j).1 = 2 ∨
      (smallParityFourTests ⟨i.val, by omega⟩ j).1 = 4 := by
    fin_cases i <;> fin_cases j <;> decide
  have hx := (hc x).mp x.property
  simp only [MulAut.orderCentralizerTest, ht, true_or, and_true,
    ← Subgroup.orderOf_coe, fastOrder_eq _ ho x hx.1 hx.2.1, cent_eq i hc, test]

private def count (i : Fin 4) (j : Fin 3) (v : SmallParityFourQuotient) : ℕ :=
  Fintype.card {w : Params //
    smallParityFourCoordinates ⟨i.val, by omega⟩ (elt i w) = v ∧ test i j (elt i w)}

private theorem fiber_count (i : Fin 4) (j : Fin 3)
    (hc : ∀ x, x ∈ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) ↔
      smallParityFourCarrier ⟨i.val, by omega⟩ x) (v : SmallParityFourQuotient) :
    Nat.card {x : smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) //
      smallParityFourMap ⟨i.val, by omega⟩ x = v ∧
      MulAut.orderCentralizerTest (smallParityFourTests ⟨i.val, by omega⟩ j) x} =
      count i j v := by
  unfold count
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact ((paramEquiv i hc).subtypeEquiv (fun w =>
    and_congr Iff.rfl (test_eq i j hc ((paramEquiv i hc) w)).symm)).symm

private theorem profile_eq_counts (i : Fin 4)
    (hc : ∀ x, x ∈ smallParityTwoCandidate (smallParityFourIndex ⟨i.val, by omega⟩) ↔
      smallParityFourCarrier ⟨i.val, by omega⟩ x) (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile ⟨i.val, by omega⟩ v =
      (count i 0 v, count i 1 v, count i 2 v) := by
  unfold smallParityFourCoordinateProfile
  rw [fiber_count i 0 hc, fiber_count i 1 hc, fiber_count i 2 hc]


private abbrev Reduced := ZMod 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private abbrev Central := ZMod 2 × ZMod 2

private def inflate (r : Reduced) (z : Central) : Params :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2, z.1, z.2)
private def cut (w : Params) : Reduced :=
  (w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1)
private def tail (w : Params) : Central := (w.2.2.2.2.2.2.1, w.2.2.2.2.2.2.2)
private def kill (x : SylowModel) : SylowModel :=
  ⟨{x.left with b8 := 0, b9 := 0}, x.right⟩

private theorem swap_cancel (a b c d : ZMod 2) : a + (b + c) = b + (a + d) ↔ c = d := by
  simp only [← add_assoc, add_comm b a, add_right_inj]

private theorem commute_kill (x y : SylowModel) :
    fastMul x y = fastMul y x ↔ fastMul (kill x) (kill y) = fastMul (kill y) (kill x) := by
  simp only [fastMul, kill, SemidirectProduct.ext_iff, Core.mk.injEq,
    add_assoc, swap_cancel, zero_add]

private theorem kill_elt (i : Fin 4) (w : Params) :
    kill (elt i w) = elt i (inflate (cut w) (0,0)) := by
  fin_cases i <;> rfl

private def shortCent (i : Fin 4) (r : Reduced) : ℕ :=
  4 * Fintype.card {s : Reduced //
    fastMul (elt i (inflate s (0,0))) (elt i (inflate r (0,0))) =
      fastMul (elt i (inflate r (0,0))) (elt i (inflate s (0,0)))}

private theorem cent_short (i : Fin 4) (w : Params) :
    cent i (elt i w) = shortCent i (cut w) := by
  let P (s : Reduced) :=
    fastMul (elt i (inflate s (0,0))) (elt i (inflate (cut w) (0,0))) =
      fastMul (elt i (inflate (cut w) (0,0))) (elt i (inflate s (0,0)))
  have hc (v : Params) :
      fastMul (elt i v) (elt i w) = fastMul (elt i w) (elt i v) ↔ P (cut v) := by
    rw [commute_kill, kill_elt, kill_elt]
  let e : {v : Params // fastMul (elt i v) (elt i w) = fastMul (elt i w) (elt i v)} ≃
      {s : Reduced // P s} × Central := {
    toFun := fun v => (⟨cut v, (hc v).mp v.property⟩, tail v)
    invFun := fun v => ⟨inflate v.1.val v.2, (hc _).mpr v.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold cent shortCent
  rw [Fintype.card_congr e, Fintype.card_prod]
  change _ * 4 = 4 * _
  exact Nat.mul_comm _ _


private def centTable (i : Fin 4) (r : Reduced) : ℕ :=
  ((![
    ([512, 64, 256, 64, 128, 64, 128, 64, 64, 64, 64, 64, 32, 64, 32, 64, 256, 64, 256, 64, 128, 64, 128, 64, 64, 64, 64, 64, 32, 64, 32, 64, 64, 64, 64, 64, 128, 64, 128, 64, 32, 64, 32, 64, 32, 64, 32, 64, 64, 64, 64, 64, 128, 64, 128, 64, 32, 64, 32, 64, 32, 64, 32, 64, 256, 64, 256, 64, 128, 64, 128, 64, 64, 64, 64, 64, 32, 64, 32, 64, 256, 64, 256, 64, 128, 64, 128, 64, 64, 64, 64, 64, 32, 64, 32, 64, 64, 64, 64, 64, 128, 64, 128, 64, 32, 64, 32, 64, 32, 64, 32, 64, 64, 64, 64, 64, 128, 64, 128, 64, 32, 64, 32, 64, 32, 64, 32, 64] : List ℕ),
    ([512, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 32, 32, 32, 32, 128, 32, 128, 32, 64, 32, 128, 32, 64, 32, 64, 32, 32, 32, 32, 32, 64, 32, 128, 32, 128, 32, 128, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 32, 128, 32, 64, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 256, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 32, 32, 32, 32, 128, 32, 128, 32, 64, 32, 128, 32, 64, 32, 64, 32, 32, 32, 32, 32, 64, 32, 128, 32, 128, 32, 128, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 32, 128, 32, 64, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32] : List ℕ),
    ([512, 64, 128, 64, 256, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 64, 32, 32, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 128, 64, 128, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 32, 32, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 256, 64, 128, 64, 256, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 64, 32, 32, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 128, 64, 128, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 32, 32, 32, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] : List ℕ),
    ([512, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 256, 64, 32, 32, 32, 32, 32, 32, 64, 32, 64, 32, 32, 32, 32, 32, 32, 32, 64, 64, 64, 64, 128, 64, 128, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 32, 256, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 128, 64, 256, 64, 32, 32, 32, 32, 32, 32, 64, 32, 64, 32, 32, 32, 32, 32, 32, 32, 64, 64, 64, 64, 128, 64, 128, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 32] : List ℕ)]) i).getD
    (r.1.val + 4 * r.2.1.val + 8 * r.2.2.1.val + 16 * r.2.2.2.1.val +
      32 * r.2.2.2.2.1.val + 64 * r.2.2.2.2.2.val) 0




private def cross (x y : SylowModel) : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
  let u : ZMod 2 := x.right.toAdd.val
  let v : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  let a := x.left
  let b := y.left
  (u * b.b3, u * b.b5,
    u * b.b6 + v * b.b5 + a.b3 * b.b2,
    u * (b.b5 + b.b6 + b.b7) + v * (b.b5 + b.b6) +
      u * v * b.b5 + a.b4 * b.b2 + a.b3 * b.b3,
    u * (b.b5 + b.b6) + v * b.b5 + a.b2 * b.b2 +
      a.b6 * b.b3 + a.b5 * (b.b4 + u * b.b3))

private theorem fastMul_comm_iff (x y : SylowModel) :
    fastMul x y = fastMul y x ↔ cross x y = cross y x := by
  simp only [fastMul, SemidirectProduct.ext_iff, Core.mk.injEq, cross, Prod.mk.injEq,
    add_assoc, swap_cancel, add_comm x.left.b2 y.left.b2,
    add_comm x.left.b3 y.left.b3, add_comm x.left.b5 y.left.b5,
    mul_comm x.right y.right, and_true, true_and]

private def shortCentFast (i : Fin 4) (r : Reduced) : ℕ :=
  4 * Fintype.card {s : Reduced //
    cross (elt i (inflate s (0,0))) (elt i (inflate r (0,0))) =
      cross (elt i (inflate r (0,0))) (elt i (inflate s (0,0)))}

private theorem shortCent_eq_fast (i : Fin 4) (r : Reduced) : shortCent i r = shortCentFast i r := by
  unfold shortCent shortCentFast
  congr 1
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun s => fastMul_comm_iff _ _)


private abbrev Binary := Bool × Bool × Bool × Bool × Bool × Bool × Bool
private abbrev FiveBool := Bool × Bool × Bool × Bool × Bool

private def zbit (b : Bool) : ZMod 2 := if b then 1 else 0
private def tbit (u v : Bool) : ZMod 4 := u.toNat + 2 * v.toNat

private theorem zbit_xor : ∀ a b, zbit (a ^^ b) = zbit a + zbit b := by decide +kernel
private theorem zbit_and : ∀ a b, zbit (a && b) = zbit a * zbit b := by decide +kernel
private theorem zbit_inj : ∀ a b, zbit a = zbit b ↔ a = b := by decide +kernel
private theorem tbit_cast : ∀ u v, ((tbit u v).cast : ZMod 2) = zbit u := by decide +kernel
private theorem tbit_high : ∀ u v, (((tbit u v).val / 2 : ℕ) : ZMod 2) = zbit v := by decide +kernel

private def fromBits (w : Binary) : Reduced :=
  (tbit w.1 w.2.1, zbit w.2.2.1, zbit w.2.2.2.1,
    zbit w.2.2.2.2.1, zbit w.2.2.2.2.2.1, zbit w.2.2.2.2.2.2)
private def toBits (r : Reduced) : Binary :=
  (r.1.val % 2 == 1, r.1.val / 2 == 1, r.2.1 == 1, r.2.2.1 == 1,
    r.2.2.2.1 == 1, r.2.2.2.2.1 == 1, r.2.2.2.2.2 == 1)
private def binaryEquiv : Binary ≃ Reduced where
  toFun := fromBits
  invFun := toBits
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private structure BState where
  c2 : Bool
  c3 : Bool
  c4 : Bool
  c5 : Bool
  c6 : Bool
  c7 : Bool
  u : Bool
  v : Bool

private def bstate (i : Fin 4) (w : Binary) : BState :=
  let u := w.1
  let v := w.2.1
  let a := w.2.2.1
  let b := w.2.2.2.1
  let c := w.2.2.2.2.1
  let d := w.2.2.2.2.2.1
  let e := w.2.2.2.2.2.2
  ![⟨a,b,c,false,d,e,u,v⟩, ⟨a,b,c,u,d,e,u,v⟩,
    ⟨a,false,b,c,d,e,u,v⟩, ⟨a,c,b,c,d,e,u,v⟩] i

private def bcross (a b : BState) : FiveBool :=
  (a.u && b.c3, a.u && b.c5,
    (a.u && b.c6) ^^ (a.v && b.c5) ^^ (a.c3 && b.c2),
    (a.u && (b.c5 ^^ b.c6 ^^ b.c7)) ^^ (a.v && (b.c5 ^^ b.c6)) ^^
      (a.u && a.v && b.c5) ^^ (a.c4 && b.c2) ^^ (a.c3 && b.c3),
    (a.u && (b.c5 ^^ b.c6)) ^^ (a.v && b.c5) ^^ (a.c2 && b.c2) ^^
      (a.c6 && b.c3) ^^ (a.c5 && (b.c4 ^^ (a.u && b.c3))))

private def liftFive (w : FiveBool) : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
  (zbit w.1, zbit w.2.1, zbit w.2.2.1, zbit w.2.2.2.1, zbit w.2.2.2.2)

private theorem liftFive_inj (a b : FiveBool) : liftFive a = liftFive b ↔ a = b := by
  simp only [liftFive, Prod.ext_iff, zbit_inj]

private theorem cross_bits (i : Fin 4) (a b : Binary) :
    cross (elt i (inflate (fromBits a) (0,0))) (elt i (inflate (fromBits b) (0,0))) =
      liftFive (bcross (bstate i a) (bstate i b)) := by
  fin_cases i <;>
    simp [cross, elt, inflate, fromBits, liftFive, bcross, bstate,
      zbit_xor, zbit_and, tbit_cast, tbit_high, add_assoc, show zbit false = 0 from rfl]

private def binaryCent (i : Fin 4) (r : Binary) : ℕ :=
  4 * Fintype.card {s : Binary // bcross (bstate i s) (bstate i r) = bcross (bstate i r) (bstate i s)}

private theorem shortCentFast_binary (i : Fin 4) (r : Binary) :
    shortCentFast i (fromBits r) = binaryCent i r := by
  unfold shortCentFast binaryCent
  congr 1
  apply Fintype.card_congr
  exact (binaryEquiv.subtypeEquiv (fun s => by
    change _ ↔ cross (elt i (inflate (fromBits s) (0,0)))
      (elt i (inflate (fromBits r) (0,0))) =
        cross (elt i (inflate (fromBits r) (0,0))) (elt i (inflate (fromBits s) (0,0)))
    rw [cross_bits, cross_bits, liftFive_inj])).symm

set_option maxHeartbeats 4000000 in
private theorem binaryCent_certificate : ∀ (i : Fin 4) (r : Binary),
    binaryCent i r = centTable i (fromBits r) := by
  rintro i ⟨u,v,a,b,c,d,e⟩
  fin_cases i <;> cases u <;> cases v <;> cases a <;> cases b <;>
    cases c <;> cases d <;> cases e <;> decide +kernel

private theorem centTable_certificate (i : Fin 4) (r : Reduced) : shortCent i r = centTable i r := by
  obtain ⟨w, rfl⟩ := binaryEquiv.surjective r
  change shortCent i (fromBits w) = centTable i (fromBits w)
  rw [shortCent_eq_fast, shortCentFast_binary]
  exact binaryCent_certificate i w


private def fastTest (i : Fin 4) (j : Fin 3) (w : Params) : Prop :=
  let t := smallParityFourTests ⟨i.val, by omega⟩ j
  fastOrder t.1 (elt i w) ∧ centTable i (cut w) = t.2.1

private instance (i : Fin 4) (j : Fin 3) (w : Params) : Decidable (fastTest i j w) := by
  unfold fastTest
  infer_instance

private def fastCount (i : Fin 4) (j : Fin 3) (v : SmallParityFourQuotient) : ℕ :=
  Fintype.card {w : Params //
    smallParityFourCoordinates ⟨i.val, by omega⟩ (elt i w) = v ∧ fastTest i j w}

private theorem count_eq_fastCount (i : Fin 4) (j : Fin 3) (v : SmallParityFourQuotient) :
    count i j v = fastCount i j v := by
  unfold count fastCount
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun w => by
    simp only [test, fastTest, cent_short, centTable_certificate])

set_option maxHeartbeats 4000000 in
private theorem counts_certificate : ∀ (i : Fin 4) (v : SmallParityFourQuotient),
    (fastCount i 0 v, fastCount i 1 v, fastCount i 2 v) =
      smallParityFourProfile ⟨i.val, by omega⟩ v := by decide +kernel

/-- The three intrinsic fiber counts for rank-four rows 0–3, assuming only the
carrier identification with the original generator closure. -/
public theorem smallParityFourCoordinateProfile_first (i : Fin 8) (hi : i.val < 4)
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex i) ↔
      smallParityFourCarrier i x) :
    ∀ v, smallParityFourCoordinateProfile i v = smallParityFourProfile i v := by
  intro v
  rw [profile_eq_counts ⟨i.val, hi⟩ hcarrier v]
  rw [count_eq_fastCount, count_eq_fastCount, count_eq_fastCount]
  exact counts_certificate ⟨i.val, hi⟩ v

end ReeTwo.SylowModel
