module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates

/-!
# Intrinsic profile counts for the last four rank-four parity candidates

Rows 4–7 use explicit eight- or seven-bit parametrizations of the proposed
carriers. Assuming those carriers equal the original generator closures, the
parametrizations identify the intrinsic counted sets with finite coordinate
filters. No multiplicativity or Frattini-kernel assertion is needed.

The cyclic-four action is first verified by a polynomial homomorphism and its
values on the ten roots. The last two core coordinates contribute four free
central choices; removing them reduces centralizer calculations to 64 or 32
representatives. Kernel reduction checks the resulting centralizer tables and
all three tests in every quotient fiber, including the repeated test in row 4
and the quadratic coordinate in row 7.

Source: Shinoda (1975), (2.3), pp. 81–82, as realized by the verified `Core`,
`RootAction`, and `Sylow` operations. Carrier equations and quotient conventions
are those fixed in `SmallParityFourCoordinates`; the numerical tables below
are certified against that multiplication, not used as external assumptions.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384
abbrev Bits8 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
def core8 (w : Bits8) : Core := ⟨0,0,w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2.1,w.2.2.2.2.2.2.1,w.2.2.2.2.2.2.2⟩
def fastAction (t : ZMod 4) (x : Core) : Core :=
  if t = 0 then x else if t = 1 then
  ⟨0,0,x.b2,x.b3,x.b3+x.b4,x.b5,x.b5+x.b6,x.b6+x.b7,
    x.b5+x.b6+x.b7+x.b8,x.b5+x.b6+x.b9⟩
  else if t = 2 then
  ⟨0,0,x.b2,x.b3,x.b4,x.b5,x.b6,x.b5+x.b7,x.b5+x.b6+x.b8,x.b5+x.b9⟩
  else ⟨0,0,x.b2,x.b3,x.b3+x.b4,x.b5,x.b5+x.b6,x.b5+x.b6+x.b7,
    x.b5+x.b7+x.b8,x.b6+x.b9⟩
/-- Polynomial form of the specified root action on the whole core. -/
def fullAction (x : Core) : Core where
  b0 := x.b0
  b1 := x.b0 + x.b1
  b2 := x.b0 + x.b1 + x.b2
  b3 := x.b1 + x.b3
  b4 := x.b0 + x.b1 + x.b3 + x.b4
  b5 := x.b0 + x.b0 * x.b1 + x.b5
  b6 := x.b0 + x.b1 + x.b0 * x.b1 + x.b5 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b6 + x.b7
  b8 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b5 + x.b6 + x.b7 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b4 + x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9

set_option maxHeartbeats 800000 in
def fullActionHom : Core →* Core where
  toFun := fullAction
  map_one' := by decide +kernel
  map_mul' x y := by
    change fullAction (Core.mul x y) = Core.mul (fullAction x) (fullAction y)
    apply Core.ext <;> simp only [fullAction, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

theorem fullAction_eq (x : Core) : fullAction x = Core.a x := by
  have h : fullActionHom = Core.a.toMonoidHom := by
    apply Core.hom_ext
    intro i
    change fullAction (Core.root i) = Core.a (Core.root i)
    rw [Core.a_root]
    exact (by decide +kernel : ∀ i : CoreRoot,
      fullAction (Core.root i) = Core.root i * (rootWord Core.root (actionCorrection i))⁻¹) i
  exact DFunLike.congr_fun h x

theorem core_mul (x y : Core) : x * y = Core.mul x y := rfl

theorem a_check (w : Bits8) : Core.a (core8 w) = fastAction 1 (core8 w) := by
  rw [← fullAction_eq]
  simp [fullAction, core8, fastAction, show (1 : ZMod 4) ≠ 0 from by decide]

theorem a_fast (x : Core) (h0 : x.b0 = 0) (h1 : x.b1 = 0) :
    Core.a x = fastAction 1 x := by
  have hx : x = core8 (x.b2,x.b3,x.b4,x.b5,x.b6,x.b7,x.b8,x.b9) := by
    cases x; simp_all [core8]
  rw [hx]
  exact a_check _

theorem fastAction_head (t : ZMod 4) (x : Core) (h0 : x.b0 = 0) (h1 : x.b1 = 0) :
    (fastAction t x).b0 = 0 ∧ (fastAction t x).b1 = 0 := by
  unfold fastAction
  split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
theorem action_check (t : ZMod 4) (w : Bits8) :
  Core.complementAction (SemidirectProduct.inr (Multiplicative.ofAdd t)) (core8 w) =
    fastAction t (core8 w) := by
  have ht : (Multiplicative.ofAdd t : FiveFour.Cyclic 4) = FiveFour.generator 4 ^ t.val :=
    (by decide +kernel : ∀ t : ZMod 4, (Multiplicative.ofAdd t : FiveFour.Cyclic 4) = FiveFour.generator 4 ^ t.val) t
  rw [ht, map_pow, map_pow]
  change (Core.complementAction FiveFour.a ^ t.val) (core8 w) = _
  rw [Core.complementAction_a]
  have hpow : ∀ n : ℕ, (Core.a ^ n) (core8 w) = (fastAction 1)^[n] (core8 w) ∧
      ((fastAction 1)^[n] (core8 w)).b0 = 0 ∧ ((fastAction 1)^[n] (core8 w)).b1 = 0 := by
    intro n
    induction n with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih.1, Function.iterate_succ_apply']
      exact ⟨a_fast _ ih.2.1 ih.2.2, fastAction_head _ _ ih.2.1 ih.2.2⟩
  rw [(hpow t.val).1]
  exact (by decide +kernel : ∀ (t : ZMod 4) (w : Bits8),
    (fastAction 1)^[t.val] (core8 w) = fastAction t (core8 w)) t w

theorem action_eq (t : ZMod 4) (x : Core) (h0 : x.b0 = 0) (h1 : x.b1 = 0) :
    Core.complementAction (SemidirectProduct.inr (Multiplicative.ofAdd t)) x =
      fastAction t x := by
  have hx : x = core8 (x.b2,x.b3,x.b4,x.b5,x.b6,x.b7,x.b8,x.b9) := by
    cases x; simp_all [core8]
  rw [hx]
  exact action_check _ _

def fastMul (x y : SylowModel) : SylowModel :=
  ⟨Core.mul x.left (fastAction x.right.toAdd y.left), x.right * y.right⟩

theorem fastMul_eq (x y : SylowModel) (h0 : y.left.b0 = 0) (h1 : y.left.b1 = 0) :
    fastMul x y = x * y := by
  apply SemidirectProduct.ext
  · simp only [fastMul, SemidirectProduct.mul_left, MonoidHom.comp_apply, core_mul]
    congr 1
    exact (action_eq x.right.toAdd y.left h0 h1).symm
  · rfl

theorem fastMul_head (x y : SylowModel)
    (hx0 : x.left.b0 = 0) (hx1 : x.left.b1 = 0)
    (hy0 : y.left.b0 = 0) (hy1 : y.left.b1 = 0) :
    (fastMul x y).left.b0 = 0 ∧ (fastMul x y).left.b1 = 0 := by
  have h := fastAction_head x.right.toAdd y.left hy0 hy1
  simp only [fastMul, Core.mul, hx0, hx1, h.1, h.2, zero_add, and_self]

def powerTest (n : ℕ) (x : SylowModel) : Prop :=
  if n = 1 then x = 1 else if n = 2 then fastMul x x = 1 ∧ x ≠ 1
  else fastMul (fastMul x x) (fastMul x x) = 1 ∧ fastMul x x ≠ 1
instance (n : ℕ) (x : SylowModel) : Decidable (powerTest n x) := by unfold powerTest; infer_instance

theorem powerTest_iff (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (x : SylowModel) (h0 : x.left.b0 = 0) (h1 : x.left.b1 = 0) :
    powerTest n x ↔ orderOf x = n := by
  have hs : fastMul x x = x ^ 2 := by rw [fastMul_eq _ _ h0 h1, pow_two]
  have hh := fastMul_head x x h0 h1 h0 h1
  have hf : fastMul (fastMul x x) (fastMul x x) = x ^ 4 := by
    rw [fastMul_eq _ _ hh.1 hh.2, hs, ← pow_two, ← pow_mul]
  rcases hn with rfl | rfl | rfl
  · simp [powerTest, orderOf_eq_one_iff]
  · simpa [powerTest, hs] using (orderOf_eq_prime_iff (x := x) (p := 2)).symm
  · simp only [powerTest, show ¬(4 : ℕ) = 1 from by decide,
      show ¬(4 : ℕ) = 2 from by decide, if_false]
    rw [hf, hs]
    constructor
    · intro h
      exact orderOf_eq_prime_pow (p := 2) (n := 1) h.2 h.1
    · intro h
      constructor
      · simpa only [h] using pow_orderOf_eq_one x
      · intro he
        have hd := orderOf_dvd_of_pow_eq_one he
        rw [h] at hd
        norm_num at hd

/-- Identify the explicit carrier with the exact candidate using the supplied certificate. -/
noncomputable def carrierEquiv {W : Type} (i : Fin 8)
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex i) ↔ smallParityFourCarrier i x)
    (encode : W → SylowModel) (decode : SylowModel → W)
    (hm : ∀ w, smallParityFourCarrier i (encode w))
    (hl : ∀ w, decode (encode w) = w)
    (hr : ∀ x, smallParityFourCarrier i x → encode (decode x) = x) :
    W ≃ smallParityTwoCandidate (smallParityFourIndex i) where
  toFun w := ⟨encode w, (hcarrier _).mpr (hm w)⟩
  invFun x := decode x.val
  left_inv := hl
  right_inv x := Subtype.ext (hr x.val ((hcarrier _).mp x.property))

theorem centralizer_transport {W : Type} [Fintype W]
    (H : Subgroup SylowModel) (e : W ≃ H) (encode : W → SylowModel)
    (he : ∀ w, (e w).val = encode w)
    (hhead : ∀ w, (encode w).left.b0 = 0 ∧ (encode w).left.b1 = 0) (w : W) :
    MulAut.commutingCard (e w) =
      Fintype.card {z : W // fastMul (encode z) (encode w) = fastMul (encode w) (encode z)} := by
  rw [← Nat.card_eq_fintype_card]
  unfold MulAut.commutingCard
  apply Nat.card_congr
  refine (e.subtypeEquiv (fun z => ?_)).symm
  rw [← Subtype.coe_inj]
  change _ ↔ (e z).val * (e w).val = (e w).val * (e z).val
  rw [he, he, fastMul_eq _ _ (hhead w).1 (hhead w).2,
    fastMul_eq _ _ (hhead z).1 (hhead z).2]

theorem count_transport {W : Type} [Fintype W]
    (i : Fin 8) (e : W ≃ smallParityTwoCandidate (smallParityFourIndex i))
    (encode : W → SylowModel) (he : ∀ w, (e w).val = encode w)
    (hhead : ∀ w, (encode w).left.b0 = 0 ∧ (encode w).left.b1 = 0)
    (c : W → ℕ)
    (hc : ∀ w, Fintype.card {z : W // fastMul (encode z) (encode w) = fastMul (encode w) (encode z)} = c w)
    (j : Fin 3)
    (ht : (smallParityFourTests i j).1 = 1 ∨ (smallParityFourTests i j).1 = 2 ∨ (smallParityFourTests i j).1 = 4)
    (ht0 : (smallParityFourTests i j).2.2 = 0)
    (v : SmallParityFourQuotient) :
    Nat.card {x : smallParityTwoCandidate (smallParityFourIndex i) //
      smallParityFourMap i x = v ∧ MulAut.orderCentralizerTest (smallParityFourTests i j) x} =
    Fintype.card {w : W // smallParityFourCoordinates i (encode w) = v ∧
      powerTest (smallParityFourTests i j).1 (encode w) ∧ c w = (smallParityFourTests i j).2.1} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine (e.subtypeEquiv (fun w => ?_)).symm
  have hcomm : MulAut.commutingCard (e w) = c w :=
    (centralizer_transport _ e encode he hhead w).trans (hc w)
  have ho : orderOf (e w) = orderOf (encode w) := by
    rw [← orderOf_injective (smallParityTwoCandidate (smallParityFourIndex i)).subtype Subtype.val_injective]
    change orderOf (e w).val = orderOf (encode w)
    rw [he]
  simp only [smallParityFourMap, he, MulAut.orderCentralizerTest, ht0, true_or,
    and_true, ho, hcomm, powerTest_iff _ ht _ (hhead w).1 (hhead w).2]


abbrev Tail := ZMod 2 × ZMod 2

def addTail (x : SylowModel) (a : Tail) : SylowModel :=
  ⟨{x.left with b8 := x.left.b8 + a.1, b9 := x.left.b9 + a.2}, x.right⟩

theorem addTail_injective (a : Tail) : Function.Injective (fun x => addTail x a) := by
  intro x y h
  have hl := congrArg SemidirectProduct.left h
  have hr := congrArg SemidirectProduct.right h
  change x.right = y.right at hr
  apply SemidirectProduct.ext _ hr
  apply Core.ext
  · simpa only [addTail] using congrArg (fun z : Core => z.b0) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b1) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b2) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b3) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b4) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b5) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b6) hl
  · simpa only [addTail] using congrArg (fun z : Core => z.b7) hl
  · have hh := congrArg (fun z : Core => z.b8) hl
    change x.left.b8 + a.1 = y.left.b8 + a.1 at hh
    exact add_right_cancel hh
  · have hh := congrArg (fun z : Core => z.b9) hl
    change x.left.b9 + a.2 = y.left.b9 + a.2 at hh
    exact add_right_cancel hh

set_option maxHeartbeats 800000 in
theorem fastMul_addTail (x y : SylowModel) (a b : Tail) (hy : y.left.b0 = 0) :
    fastMul (addTail x a) (addTail y b) = addTail (fastMul x y) (a + b) := by
  apply SemidirectProduct.ext
  · simp only [fastMul, addTail]
    unfold fastAction
    split_ifs <;> apply Core.ext <;> simp only [Core.mul, hy, zero_mul, mul_zero, add_zero]
    all_goals dsimp
    all_goals ring
  · rfl

theorem fastComm_addTail (x y : SylowModel) (a b : Tail)
    (hx : x.left.b0 = 0) (hy : y.left.b0 = 0) :
    fastMul (addTail x a) (addTail y b) = fastMul (addTail y b) (addTail x a) ↔
      fastMul x y = fastMul y x := by
  rw [fastMul_addTail _ _ _ _ hy, fastMul_addTail _ _ _ _ hx, add_comm b a]
  exact (addTail_injective (a + b)).eq_iff

def tailEquiv {B : Type} (P : B → Prop) (Q : B × Tail → Prop)
    (h : ∀ z, Q z ↔ P z.1) : {z // Q z} ≃ {b // P b} × Tail where
  toFun z := (⟨z.val.1, (h z.val).mp z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val,z.2), (h _).mpr z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two final coordinates are independent central choices in each count. -/
theorem centralizer_tail {B : Type} [Fintype B] (encode : B → SylowModel)
    (hhead : ∀ b, (encode b).left.b0 = 0) (w : B × Tail) :
    Fintype.card {z : B × Tail //
      fastMul (addTail (encode z.1) z.2) (addTail (encode w.1) w.2) =
      fastMul (addTail (encode w.1) w.2) (addTail (encode z.1) z.2)} =
    Fintype.card {z : B // fastMul (encode z) (encode w.1) = fastMul (encode w.1) (encode z)} * 4 := by
  rw [Fintype.card_congr (tailEquiv (fun z : B => fastMul (encode z) (encode w.1) = fastMul (encode w.1) (encode z)) _ (fun z =>
    fastComm_addTail _ _ z.2 w.2 (hhead z.1) (hhead w.1))), Fintype.card_prod]
  rfl


abbrev Base8 := ZMod 4 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
abbrev Base7 := ZMod 4 × ZMod 2 × ZMod 2 × ZMod 2
abbrev Param8 := Base8 × Tail
abbrev Param7 := Base7 × Tail

def base4 (w : Base8) : SylowModel :=
  ⟨⟨0, 0, w.2.1, 0, w.2.2.1, 0, w.2.2.2.1, w.2.2.2.2, 0, 0⟩, Multiplicative.ofAdd w.1⟩
def encode4 (w : Param8) : SylowModel := addTail (base4 w.1) w.2
def decode4 (x : SylowModel) : Param8 :=
  ((x.right.toAdd, x.left.b2, x.left.b4, x.left.b6, x.left.b7), (x.left.b8, x.left.b9))
theorem encode4_mem (w : Param8) : smallParityFourCarrier 4 (encode4 w) :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem decode4_encode (w) : decode4 (encode4 w) = w := by
  rcases w with ⟨w,a,b⟩
  simp [decode4, encode4, base4, addTail]
theorem encode4_decode (x : SylowModel) (hx : smallParityFourCarrier 4 x) : encode4 (decode4 x) = x := by
  change x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b3 = 0 ∧ x.left.b5 = 0 at hx
  rcases hx with ⟨h0,h1,h3,h5⟩
  apply SemidirectProduct.ext
  · apply Core.ext <;> simp [encode4, decode4, base4, addTail, h0,h1,h3,h5]
  · rfl

def centralizerBase4 (w : Base8) : ℕ :=
  ([256, 128, 128, 128, 64, 64, 64, 64, 128, 128, 128, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 128, 128, 128, 64, 64, 64, 64, 128, 128, 128, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64] : List ℕ).getD (16 * w.1.val + 1 * (w.2.1).val + 2 * (w.2.2.1).val + 4 * (w.2.2.2.1).val + 8 * (w.2.2.2.2).val) 0

set_option maxHeartbeats 800000 in
theorem centralizerBase4_check : ∀ w : Base8,
    Fintype.card {z : Base8 // fastMul (base4 z) (base4 w) =
      fastMul (base4 w) (base4 z)} * 4 = centralizerBase4 w := by decide +kernel

def centralizer4 (w : Param8) : ℕ := centralizerBase4 w.1

theorem centralizer4_check (w : Param8) :
    Fintype.card {z : Param8 // fastMul (encode4 z) (encode4 w) =
      fastMul (encode4 w) (encode4 z)} = centralizer4 w :=
  (centralizer_tail base4 (fun _ => rfl) w).trans (centralizerBase4_check w.1)

set_option maxHeartbeats 800000 in
theorem counts4 : ∀ v : SmallParityFourQuotient,
  (Fintype.card {w : Param8 // smallParityFourCoordinates 4 (encode4 w) = v ∧
    powerTest (smallParityFourTests 4 0).1 (encode4 w) ∧ centralizer4 w = (smallParityFourTests 4 0).2.1},
   Fintype.card {w : Param8 // smallParityFourCoordinates 4 (encode4 w) = v ∧
    powerTest (smallParityFourTests 4 1).1 (encode4 w) ∧ centralizer4 w = (smallParityFourTests 4 1).2.1},
   Fintype.card {w : Param8 // smallParityFourCoordinates 4 (encode4 w) = v ∧
    powerTest (smallParityFourTests 4 2).1 (encode4 w) ∧ centralizer4 w = (smallParityFourTests 4 2).2.1}) =
    smallParityFourProfile 4 v := by decide +kernel

def base5 (w : Base8) : SylowModel :=
  ⟨⟨0, 0, w.2.1, 0, w.2.2.1, (w.1.val : ZMod 2), w.2.2.2.1, w.2.2.2.2, 0, 0⟩, Multiplicative.ofAdd w.1⟩
def encode5 (w : Param8) : SylowModel := addTail (base5 w.1) w.2
def decode5 (x : SylowModel) : Param8 :=
  ((x.right.toAdd, x.left.b2, x.left.b4, x.left.b6, x.left.b7), (x.left.b8, x.left.b9))
theorem encode5_mem (w : Param8) : smallParityFourCarrier 5 (encode5 w) :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem decode5_encode (w) : decode5 (encode5 w) = w := by
  rcases w with ⟨w,a,b⟩
  simp [decode5, encode5, base5, addTail]
theorem encode5_decode (x : SylowModel) (hx : smallParityFourCarrier 5 x) : encode5 (decode5 x) = x := by
  change x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b3 = 0 ∧ x.left.b5 = (x.right.toAdd.val : ZMod 2) at hx
  rcases hx with ⟨h0,h1,h3,h5⟩
  apply SemidirectProduct.ext
  · apply Core.ext <;> simp [encode5, decode5, base5, addTail, h0,h1,h3,h5]
  · rfl

def centralizerBase5 (w : Base8) : ℕ :=
  ([256, 128, 64, 64, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 128, 128, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] : List ℕ).getD (16 * w.1.val + 1 * (w.2.1).val + 2 * (w.2.2.1).val + 4 * (w.2.2.2.1).val + 8 * (w.2.2.2.2).val) 0

set_option maxHeartbeats 800000 in
theorem centralizerBase5_check : ∀ w : Base8,
    Fintype.card {z : Base8 // fastMul (base5 z) (base5 w) =
      fastMul (base5 w) (base5 z)} * 4 = centralizerBase5 w := by decide +kernel

def centralizer5 (w : Param8) : ℕ := centralizerBase5 w.1

theorem centralizer5_check (w : Param8) :
    Fintype.card {z : Param8 // fastMul (encode5 z) (encode5 w) =
      fastMul (encode5 w) (encode5 z)} = centralizer5 w :=
  (centralizer_tail base5 (fun _ => rfl) w).trans (centralizerBase5_check w.1)

set_option maxHeartbeats 800000 in
theorem counts5 : ∀ v : SmallParityFourQuotient,
  (Fintype.card {w : Param8 // smallParityFourCoordinates 5 (encode5 w) = v ∧
    powerTest (smallParityFourTests 5 0).1 (encode5 w) ∧ centralizer5 w = (smallParityFourTests 5 0).2.1},
   Fintype.card {w : Param8 // smallParityFourCoordinates 5 (encode5 w) = v ∧
    powerTest (smallParityFourTests 5 1).1 (encode5 w) ∧ centralizer5 w = (smallParityFourTests 5 1).2.1},
   Fintype.card {w : Param8 // smallParityFourCoordinates 5 (encode5 w) = v ∧
    powerTest (smallParityFourTests 5 2).1 (encode5 w) ∧ centralizer5 w = (smallParityFourTests 5 2).2.1}) =
    smallParityFourProfile 5 v := by decide +kernel

def base6 (w : Base7) : SylowModel :=
  ⟨⟨0, 0, 0, w.2.1, w.2.2.1, 0, 0, w.2.2.2, 0, 0⟩, Multiplicative.ofAdd w.1⟩
def encode6 (w : Param7) : SylowModel := addTail (base6 w.1) w.2
def decode6 (x : SylowModel) : Param7 :=
  ((x.right.toAdd, x.left.b3, x.left.b4, x.left.b7), (x.left.b8, x.left.b9))
theorem encode6_mem (w : Param7) : smallParityFourCarrier 6 (encode6 w) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem decode6_encode (w) : decode6 (encode6 w) = w := by
  rcases w with ⟨w,a,b⟩
  simp [decode6, encode6, base6, addTail]
theorem encode6_decode (x : SylowModel) (hx : smallParityFourCarrier 6 x) : encode6 (decode6 x) = x := by
  change x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b2 = 0 ∧ x.left.b5 = 0 ∧ x.left.b6 = 0 at hx
  rcases hx with ⟨h0,h1,h2,h5,h6⟩
  apply SemidirectProduct.ext
  · apply Core.ext <;> simp [encode6, decode6, base6, addTail, h0,h1,h2,h5,h6]
  · rfl

def centralizerBase6 (w : Base7) : ℕ :=
  ([128, 64, 128, 64, 64, 64, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 128, 64, 128, 64, 64, 64, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32] : List ℕ).getD (8 * w.1.val + 1 * (w.2.1).val + 2 * (w.2.2.1).val + 4 * (w.2.2.2).val) 0

set_option maxHeartbeats 800000 in
theorem centralizerBase6_check : ∀ w : Base7,
    Fintype.card {z : Base7 // fastMul (base6 z) (base6 w) =
      fastMul (base6 w) (base6 z)} * 4 = centralizerBase6 w := by decide +kernel

def centralizer6 (w : Param7) : ℕ := centralizerBase6 w.1

theorem centralizer6_check (w : Param7) :
    Fintype.card {z : Param7 // fastMul (encode6 z) (encode6 w) =
      fastMul (encode6 w) (encode6 z)} = centralizer6 w :=
  (centralizer_tail base6 (fun _ => rfl) w).trans (centralizerBase6_check w.1)

set_option maxHeartbeats 800000 in
theorem counts6 : ∀ v : SmallParityFourQuotient,
  (Fintype.card {w : Param7 // smallParityFourCoordinates 6 (encode6 w) = v ∧
    powerTest (smallParityFourTests 6 0).1 (encode6 w) ∧ centralizer6 w = (smallParityFourTests 6 0).2.1},
   Fintype.card {w : Param7 // smallParityFourCoordinates 6 (encode6 w) = v ∧
    powerTest (smallParityFourTests 6 1).1 (encode6 w) ∧ centralizer6 w = (smallParityFourTests 6 1).2.1},
   Fintype.card {w : Param7 // smallParityFourCoordinates 6 (encode6 w) = v ∧
    powerTest (smallParityFourTests 6 2).1 (encode6 w) ∧ centralizer6 w = (smallParityFourTests 6 2).2.1}) =
    smallParityFourProfile 6 v := by decide +kernel

def base7 (w : Base7) : SylowModel :=
  ⟨⟨0, 0, w.2.1, 0, w.2.2.1, (w.1.val : ZMod 2), (w.1.val : ZMod 2) + ((w.1.val / 2 : ℕ) : ZMod 2), w.2.2.2, 0, 0⟩, Multiplicative.ofAdd w.1⟩
def encode7 (w : Param7) : SylowModel := addTail (base7 w.1) w.2
def decode7 (x : SylowModel) : Param7 :=
  ((x.right.toAdd, x.left.b2, x.left.b4, x.left.b7), (x.left.b8, x.left.b9))
theorem encode7_mem (w : Param7) : smallParityFourCarrier 7 (encode7 w) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  change (w.1.1.val : ZMod 2) + ((w.1.1.val : ZMod 2) + ((w.1.1.val / 2 : ℕ) : ZMod 2)) +
    ((w.1.1.val / 2 : ℕ) : ZMod 2) = 0
  ring_nf
  reduce_mod_char
theorem decode7_encode (w) : decode7 (encode7 w) = w := by
  rcases w with ⟨w,a,b⟩
  simp [decode7, encode7, base7, addTail]
theorem encode7_decode (x : SylowModel) (hx : smallParityFourCarrier 7 x) : encode7 (decode7 x) = x := by
  change x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b3 = 0 ∧ x.left.b5 = (x.right.toAdd.val : ZMod 2) ∧ x.left.b5 + x.left.b6 + ((x.right.toAdd.val / 2 : ℕ) : ZMod 2) = 0 at hx
  rcases hx with ⟨h0,h1,h3,h5,h6⟩
  have hb : x.left.b6 = (x.right.toAdd.val : ZMod 2) + ((x.right.toAdd.val / 2 : ℕ) : ZMod 2) := by
    have h := (by decide : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c) _ _ _ h6
    simpa only [h5] using h
  apply SemidirectProduct.ext
  · apply Core.ext <;> simp [encode7, decode7, base7, addTail, h0,h1,h3,h5,hb]
  · rfl

def centralizerBase7 (w : Base7) : ℕ :=
  ([128, 64, 32, 32, 64, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 64, 64, 32, 32, 128, 64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] : List ℕ).getD (8 * w.1.val + 1 * (w.2.1).val + 2 * (w.2.2.1).val + 4 * (w.2.2.2).val) 0

set_option maxHeartbeats 800000 in
theorem centralizerBase7_check : ∀ w : Base7,
    Fintype.card {z : Base7 // fastMul (base7 z) (base7 w) =
      fastMul (base7 w) (base7 z)} * 4 = centralizerBase7 w := by decide +kernel

def centralizer7 (w : Param7) : ℕ := centralizerBase7 w.1

theorem centralizer7_check (w : Param7) :
    Fintype.card {z : Param7 // fastMul (encode7 z) (encode7 w) =
      fastMul (encode7 w) (encode7 z)} = centralizer7 w :=
  (centralizer_tail base7 (fun _ => rfl) w).trans (centralizerBase7_check w.1)

set_option maxHeartbeats 800000 in
theorem counts7 : ∀ v : SmallParityFourQuotient,
  (Fintype.card {w : Param7 // smallParityFourCoordinates 7 (encode7 w) = v ∧
    powerTest (smallParityFourTests 7 0).1 (encode7 w) ∧ centralizer7 w = (smallParityFourTests 7 0).2.1},
   Fintype.card {w : Param7 // smallParityFourCoordinates 7 (encode7 w) = v ∧
    powerTest (smallParityFourTests 7 1).1 (encode7 w) ∧ centralizer7 w = (smallParityFourTests 7 1).2.1},
   Fintype.card {w : Param7 // smallParityFourCoordinates 7 (encode7 w) = v ∧
    powerTest (smallParityFourTests 7 2).1 (encode7 w) ∧ centralizer7 w = (smallParityFourTests 7 2).2.1}) =
    smallParityFourProfile 7 v := by decide +kernel

theorem profile_transport {W : Type} [Fintype W]
    (i : Fin 8) (e : W ≃ smallParityTwoCandidate (smallParityFourIndex i))
    (encode : W → SylowModel) (he : ∀ w, (e w).val = encode w)
    (hhead : ∀ w, (encode w).left.b0 = 0 ∧ (encode w).left.b1 = 0)
    (c : W → ℕ)
    (hc : ∀ w, Fintype.card {z : W // fastMul (encode z) (encode w) = fastMul (encode w) (encode z)} = c w)
    (ht : ∀ j, (smallParityFourTests i j).1 = 1 ∨ (smallParityFourTests i j).1 = 2 ∨ (smallParityFourTests i j).1 = 4)
    (ht0 : ∀ j, (smallParityFourTests i j).2.2 = 0)
    (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile i v =
    (Fintype.card {w : W // smallParityFourCoordinates i (encode w) = v ∧
      powerTest (smallParityFourTests i 0).1 (encode w) ∧ c w = (smallParityFourTests i 0).2.1},
     Fintype.card {w : W // smallParityFourCoordinates i (encode w) = v ∧
      powerTest (smallParityFourTests i 1).1 (encode w) ∧ c w = (smallParityFourTests i 1).2.1},
     Fintype.card {w : W // smallParityFourCoordinates i (encode w) = v ∧
      powerTest (smallParityFourTests i 2).1 (encode w) ∧ c w = (smallParityFourTests i 2).2.1}) := by
  unfold smallParityFourCoordinateProfile
  rw [count_transport i e encode he hhead c hc 0 (ht 0) (ht0 0),
    count_transport i e encode he hhead c hc 1 (ht 1) (ht0 1),
    count_transport i e encode he hhead c hc 2 (ht 2) (ht0 2)]

theorem profile4
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex 4) ↔ smallParityFourCarrier 4 x)
    (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile 4 v = smallParityFourProfile 4 v := by
  let e := carrierEquiv 4 hcarrier encode4 decode4 encode4_mem decode4_encode encode4_decode
  rw [profile_transport 4 e encode4 (fun _ => rfl) (fun _ => ⟨rfl,rfl⟩)
    centralizer4 centralizer4_check (by decide +kernel) (by decide +kernel)]
  exact counts4 v

theorem profile5
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex 5) ↔ smallParityFourCarrier 5 x)
    (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile 5 v = smallParityFourProfile 5 v := by
  let e := carrierEquiv 5 hcarrier encode5 decode5 encode5_mem decode5_encode encode5_decode
  rw [profile_transport 5 e encode5 (fun _ => rfl) (fun _ => ⟨rfl,rfl⟩)
    centralizer5 centralizer5_check (by decide +kernel) (by decide +kernel)]
  exact counts5 v

theorem profile6
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex 6) ↔ smallParityFourCarrier 6 x)
    (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile 6 v = smallParityFourProfile 6 v := by
  let e := carrierEquiv 6 hcarrier encode6 decode6 encode6_mem decode6_encode encode6_decode
  rw [profile_transport 6 e encode6 (fun _ => rfl) (fun _ => ⟨rfl,rfl⟩)
    centralizer6 centralizer6_check (by decide +kernel) (by decide +kernel)]
  exact counts6 v

theorem profile7
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex 7) ↔ smallParityFourCarrier 7 x)
    (v : SmallParityFourQuotient) :
    smallParityFourCoordinateProfile 7 v = smallParityFourProfile 7 v := by
  let e := carrierEquiv 7 hcarrier encode7 decode7 encode7_mem decode7_encode encode7_decode
  rw [profile_transport 7 e encode7 (fun _ => rfl) (fun _ => ⟨rfl,rfl⟩)
    centralizer7 centralizer7_check (by decide +kernel) (by decide +kernel)]
  exact counts7 v

/-- The last four fixed coordinate profiles count the intrinsic tests in the exact candidates. -/
public theorem smallParityFourCoordinateProfile_last (i : Fin 8) (hi : 4 ≤ i.val)
    (hcarrier : ∀ x : SylowModel, x ∈ smallParityTwoCandidate (smallParityFourIndex i) ↔ smallParityFourCarrier i x) :
    ∀ v, smallParityFourCoordinateProfile i v = smallParityFourProfile i v := by
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · exact profile4 hcarrier
  · exact profile5 hcarrier
  · exact profile6 hcarrier
  · exact profile7 hcarrier

end ReeTwo.SylowModel
