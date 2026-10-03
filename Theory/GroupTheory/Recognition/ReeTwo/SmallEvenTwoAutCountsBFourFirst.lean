module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesBFour
public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates

/-!
# Intrinsic rank-four B fiber counts

For the first five rank-four candidates, the carrier equations have right
coordinate one and eight free binary core coordinates.  The displayed
coordinate map therefore has sixteen-element fibers. We transport the three
intrinsic order/centralizer tests along this parametrization. Verified bit-vector
multiplication computes all 256 commuting partners simultaneously; population
counts then give the centralizer cardinalities in the exact candidate. Kernel
reduction checks the resulting fiber counts, sharing repeated tests.

The packed counting method follows `SmallEvenAutCountsA512Arithmetic`.

Source: Shinoda (1975), (2.3), pp. 81–82; the coordinate and carrier equations
are fixed in `SmallEvenTwoAutCoordinatesBFour`.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB

open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

private def row (i : Fin 5) : Fin 7 := ⟨i.val, by omega⟩
private abbrev Bits := Fin 4 → ZMod 2

private def point (i : Fin 5) (v w : Bits) : Core :=
  (![⟨v 0 + v 1 + v 3 + v 2, v 2, v 3, 0, v 3,
       w 0, w 1, v 1 + w 1, w 2, w 3⟩,
     ⟨v 0 + v 1 + v 3, v 2, 0, v 3, 0,
       w 0, w 1, v 1 + v 2, w 2, w 3⟩,
     ⟨v 3 + v 2 + v 0 + v 1, v 0 + v 1, v 0 + v 1, v 2, v 0 + v 1,
       w 0, v 1 + w 0, w 1, w 2, w 3⟩,
     ⟨v 3 + v 1 + v 2, v 2, v 3 + v 1 + v 2, v 1, v 3 + v 1 + v 2,
       w 0, w 1, v 0 + w 1 + v 1 + v 2, w 2, w 3⟩,
     ⟨v 0 + v 3, v 3, v 2, v 3, v 3,
       w 0, w 1, w 2, v 1 + v 3 * v 2 + w 1 + v 2, w 3⟩] : Fin 5 → Core) i

private def rest (i : Fin 5) (c : Core) : Bits :=
  (![![c.b5,c.b6,c.b8,c.b9], ![c.b5,c.b6,c.b8,c.b9],
     ![c.b5,c.b7,c.b8,c.b9], ![c.b5,c.b6,c.b8,c.b9],
     ![c.b5,c.b6,c.b7,c.b9]] : Fin 5 → Bits) i

private def embed (c : Core) : SylowModel := SemidirectProduct.inl c

private theorem point_carrier (i : Fin 5) (v w : Bits) :
    rankFourCarrier (row i) (embed (point i v w)) := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem point_coordinates (i : Fin 5) (v w : Bits) :
    rankFourCoordinates (row i) (embed (point i v w)) = Multiplicative.ofAdd v := by
  change (rankFourCoordinates (row i) (embed (point i v w))).toAdd = v
  funext j
  fin_cases i <;> fin_cases j <;>
    dsimp [rankFourCoordinates, row, point, embed, SemidirectProduct.inl] <;>
    ring_nf <;> reduce_mod_char

private theorem point_rest (i : Fin 5) (v w : Bits) : rest i (point i v w) = w := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem point_reconstruct (i : Fin 5) (c : Core)
    (h : rankFourCarrier (row i) (embed c)) :
    point i (rankFourCoordinates (row i) (embed c)).toAdd (rest i c) = c := by
  decide +kernel +revert

private theorem carrier_right (i : Fin 5) (x : SylowModel)
    (h : rankFourCarrier (row i) x) : x.right = 1 := by
  fin_cases i <;> exact h.1

private theorem embed_left (x : SylowModel) (h : x.right = 1) : embed x.left = x := by
  apply SemidirectProduct.ext
  · rfl
  · exact h.symm

private def parametrization (i : Fin 5)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex (row i)) ↔ rankFourCarrier (row i) x) :
    (Bits × Bits) ≃ smallEvenCandidate (rankFourIndex (row i)) where
  toFun p := ⟨embed (point i p.1 p.2), (hcarrier _).mpr (point_carrier i _ _)⟩
  invFun x := ((rankFourMap (row i) x).toAdd, rest i x.val.left)
  left_inv p := Prod.ext (congrArg Multiplicative.toAdd (point_coordinates i _ _))
    (point_rest i _ _)
  right_inv x := by
    apply Subtype.ext
    have hx := (hcarrier x.val).mp x.property
    have he := embed_left x.val (carrier_right i x.val hx)
    change embed (point i (rankFourCoordinates (row i) x.val).toAdd
      (rest i x.val.left)) = x.val
    have hp := point_reconstruct i x.val.left (by rw [he]; exact hx)
    rw [← he]
    exact congrArg embed hp

private def bits (n : Fin 16) : Bits :=
  ![(n.val : ZMod 2), (n.val / 2 : ℕ), (n.val / 4 : ℕ), (n.val / 8 : ℕ)]

private def number (w : Bits) : Fin 16 :=
  Fin.ofNat 16 ((w 0).val + 2*(w 1).val + 4*(w 2).val + 8*(w 3).val)

private def bitsEquiv : Fin 16 ≃ Bits where
  toFun := bits
  invFun := number
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pair (n : Fin 256) : Bits × Bits :=
  (bits ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩,
    bits ⟨n.val / 16, by omega⟩)

private def pairNumber (p : Bits × Bits) : Fin 256 :=
  ⟨(number p.1).val + 16*(number p.2).val, by have := (number p.1).isLt; have := (number p.2).isLt; omega⟩

private def pairEquiv : Fin 256 ≃ Bits × Bits where
  toFun := pair
  invFun := pairNumber
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def centralCount (i : Fin 5) (c : Core) : ℕ :=
  (Finset.univ.filter (fun n : Fin 256 =>
    point i (pair n).1 (pair n).2 * c = c * point i (pair n).1 (pair n).2)).card


-- Evaluate all 256 commuting partners simultaneously with verified bit operations.
private def zbit (b : Bool) : ZMod 2 := if b then 1 else 0
private theorem zbit_xor : ∀ a b, zbit (a ^^ b) = zbit a + zbit b := by decide +kernel
private theorem zbit_and : ∀ a b, zbit (a && b) = zbit a * zbit b := by decide +kernel
private theorem zbit_inj : ∀ a b, zbit a = zbit b ↔ a = b := by decide +kernel
private structure PCore where
  b0 : BitVec 256
  b1 : BitVec 256
  b2 : BitVec 256
  b3 : BitVec 256
  b4 : BitVec 256
  b5 : BitVec 256
  b6 : BitVec 256
  b7 : BitVec 256
  b8 : BitVec 256
  b9 : BitVec 256
  deriving DecidableEq
private def pmul (x y : PCore) : PCore where
  b0 := (x.b0 ^^^ y.b0)
  b1 := (x.b1 ^^^ y.b1)
  b2 := (x.b2 ^^^ y.b2)
  b3 := (x.b3 ^^^ y.b3)
  b4 := (x.b4 ^^^ y.b4)
  b5 := ((((x.b5 ^^^ (x.b2 &&& y.b0)) ^^^ (x.b3 &&& y.b0)) ^^^ (x.b1 &&& y.b1)) ^^^ y.b5)
  b6 := ((((x.b6 ^^^ (x.b3 &&& y.b0)) ^^^ (x.b4 &&& y.b0)) ^^^ (x.b2 &&& y.b1)) ^^^ y.b6)
  b7 := ((((x.b7 ^^^ (x.b4 &&& y.b0)) ^^^ (x.b4 &&& y.b1)) ^^^ (x.b3 &&& y.b2)) ^^^ y.b7)
  b8 := ((((x.b8 ^^^ (x.b4 &&& y.b1)) ^^^ (x.b4 &&& y.b2)) ^^^ (x.b3 &&& y.b3)) ^^^ y.b8)
  b9 := (((((((((((((((((((x.b9 ^^^ (x.b3 &&& y.b0)) ^^^ ((x.b2 &&& x.b4) &&& y.b0)) ^^^ ((x.b3 &&& x.b4) &&& y.b0)) ^^^ (x.b8 &&& y.b0)) ^^^ ((x.b2 &&& x.b3) &&& y.b1)) ^^^ (x.b4 &&& y.b1)) ^^^ ((x.b1 &&& x.b4) &&& y.b1)) ^^^ (x.b7 &&& y.b1)) ^^^ ((x.b4 &&& y.b0) &&& y.b1)) ^^^ (x.b2 &&& y.b2)) ^^^ (x.b6 &&& y.b3)) ^^^ ((x.b3 &&& y.b0) &&& y.b3)) ^^^ ((x.b4 &&& y.b0) &&& y.b3)) ^^^ ((x.b2 &&& y.b1) &&& y.b3)) ^^^ (x.b5 &&& y.b4)) ^^^ ((x.b2 &&& y.b0) &&& y.b4)) ^^^ ((x.b3 &&& y.b0) &&& y.b4)) ^^^ ((x.b1 &&& y.b1) &&& y.b4)) ^^^ y.b9)
private def getCore (c : PCore) (n : Fin 256) : Core :=
  ⟨zbit (c.b0.getLsbD n.val), zbit (c.b1.getLsbD n.val), zbit (c.b2.getLsbD n.val), zbit (c.b3.getLsbD n.val), zbit (c.b4.getLsbD n.val), zbit (c.b5.getLsbD n.val), zbit (c.b6.getLsbD n.val), zbit (c.b7.getLsbD n.val), zbit (c.b8.getLsbD n.val), zbit (c.b9.getLsbD n.val)⟩
private theorem get_pmul (x y : PCore) (n : Fin 256) :
    getCore (pmul x y) n = getCore x n * getCore y n := by
  change getCore (pmul x y) n = Core.mul (getCore x n) (getCore y n)
  apply Core.ext <;>
    simp only [getCore, pmul, Core.mul, zbit_xor, zbit_and,
      BitVec.getLsbD_xor, BitVec.getLsbD_and]
private def eqMask (x y : PCore) : BitVec 256 :=
  ~~~(x.b0 ^^^ y.b0) &&&
    ~~~(x.b1 ^^^ y.b1) &&&
    ~~~(x.b2 ^^^ y.b2) &&&
    ~~~(x.b3 ^^^ y.b3) &&&
    ~~~(x.b4 ^^^ y.b4) &&&
    ~~~(x.b5 ^^^ y.b5) &&&
    ~~~(x.b6 ^^^ y.b6) &&&
    ~~~(x.b7 ^^^ y.b7) &&&
    ~~~(x.b8 ^^^ y.b8) &&&
    ~~~(x.b9 ^^^ y.b9)
private theorem eqMask_spec (x y : PCore) (n : Fin 256) :
    (eqMask x y).getLsbD n.val = true ↔ getCore x n = getCore y n := by
  simp [eqMask, getCore, Core.mk.injEq, zbit_inj, n.isLt, and_assoc]
private def replicate (b : Bool) : BitVec 256 := if b then BitVec.allOnes 256 else 0
private theorem get_replicate (b : Bool) (n : Fin 256) : (replicate b).getLsbD n.val = b := by
  cases b <;> simp only [replicate, Bool.false_eq_true, if_false, if_true,
    BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, n.isLt, decide_true]
private def packCore (c : Core) : PCore :=
  ⟨replicate (c.b0 == 1), replicate (c.b1 == 1), replicate (c.b2 == 1), replicate (c.b3 == 1), replicate (c.b4 == 1), replicate (c.b5 == 1), replicate (c.b6 == 1), replicate (c.b7 == 1), replicate (c.b8 == 1), replicate (c.b9 == 1)⟩
private theorem get_packCore (c : Core) (n : Fin 256) : getCore (packCore c) n = c := by
  have hb : ∀ b : ZMod 2, zbit (b == 1) = b := by decide +kernel
  apply Core.ext <;> simp only [getCore, packCore, get_replicate, hb]

private abbrev PBits := Fin 4 → BitVec 256
private def getBits (v : PBits) (n : Fin 256) : Bits := fun j => zbit ((v j).getLsbD n.val)
private def ppoint (i : Fin 5) (v w : PBits) : PCore :=
  (![⟨v 0 ^^^ v 1 ^^^ v 3 ^^^ v 2, v 2, v 3, 0, v 3,
       w 0, w 1, v 1 ^^^ w 1, w 2, w 3⟩,
     ⟨v 0 ^^^ v 1 ^^^ v 3, v 2, 0, v 3, 0,
       w 0, w 1, v 1 ^^^ v 2, w 2, w 3⟩,
     ⟨v 3 ^^^ v 2 ^^^ v 0 ^^^ v 1, v 0 ^^^ v 1, v 0 ^^^ v 1, v 2, v 0 ^^^ v 1,
       w 0, v 1 ^^^ w 0, w 1, w 2, w 3⟩,
     ⟨v 3 ^^^ v 1 ^^^ v 2, v 2, v 3 ^^^ v 1 ^^^ v 2, v 1, v 3 ^^^ v 1 ^^^ v 2,
       w 0, w 1, v 0 ^^^ w 1 ^^^ v 1 ^^^ v 2, w 2, w 3⟩,
     ⟨v 0 ^^^ v 3, v 3, v 2, v 3, v 3,
       w 0, w 1, w 2, v 1 ^^^ v 3 &&& v 2 ^^^ w 1 ^^^ v 2, w 3⟩] : Fin 5 → PCore) i

private theorem get_ppoint (i : Fin 5) (v w : PBits) (n : Fin 256) :
    getCore (ppoint i v w) n = point i (getBits v n) (getBits w n) := by
  fin_cases i <;> apply Core.ext <;>
    simp only [getCore, ppoint, point, getBits, BitVec.getLsbD_xor,
      BitVec.getLsbD_and, BitVec.getLsbD_zero, BitVec.ofNat_eq_ofNat,
      Matrix.cons_val, Fin.reduceFinMk, zbit_xor, zbit_and, show zbit false = 0 from rfl]
private def vSeeds : PBits :=
  ![BitVec.ofNat 256 77194726158210796949047323339125271902179989777093709359638389338608753093290,
    BitVec.ofNat 256 92633671389852956338856788006950326282615987732512451231566067206330503711948,
    BitVec.ofNat 256 108980789870415242751596221184647442685430573802955824978313020242741769072880,
    BitVec.ofNat 256 115341536360906404779899502576747487978354537254490211650198994186870666100480]
private def wSeeds : PBits :=
  ![BitVec.ofNat 256 115790322417210952336529717160220497262186272106556906860092653394915770695680,
    BitVec.ofNat 256 115792089210356248762697446947946071893095522863849111501270640965525260206080,
    BitVec.ofNat 256 115792089237316195417293883273301227089774477609353836086800156426807153786880,
    BitVec.ofNat 256 115792089237316195423570985008687907852929702298719625575994209400481361428480]
private theorem get_vSeeds : ∀ n, getBits vSeeds n = (pair n).1 := by decide +kernel
private theorem get_wSeeds : ∀ n, getBits wSeeds n = (pair n).2 := by decide +kernel
private theorem pop_sum (x : BitVec 256) (n : ℕ) :
    x.cpopNatRec n 0 = ∑ k ∈ Finset.range n, (x.getLsbD k).toNat := by
  induction n with
  | zero => simp [BitVec.cpopNatRec]
  | succ n ih =>
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, ih, Finset.sum_range_succ, Nat.zero_add]
private theorem pop_card (x : BitVec 256) :
    (Finset.univ.filter (fun n : Fin 256 => x.getLsbD n.val = true)).card =
      x.cpopNatRec 256 0 := by
  rw [pop_sum, ← Fin.sum_univ_eq_sum_range]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro n _
  cases x.getLsbD n.val <;> rfl

private def fastCentralCount (i : Fin 5) (c : Core) : ℕ :=
  (eqMask (pmul (ppoint i vSeeds wSeeds) (packCore c))
    (pmul (packCore c) (ppoint i vSeeds wSeeds))).cpopNatRec 256 0

private theorem centralCount_fast (i : Fin 5) (c : Core) :
    centralCount i c = fastCentralCount i c := by
  unfold centralCount fastCentralCount
  rw [← pop_card]
  congr 1
  apply Finset.filter_congr
  intro n _
  rw [eqMask_spec, get_pmul, get_pmul, get_ppoint, get_packCore,
    get_vSeeds, get_wSeeds]

private theorem centralCount_eq (i : Fin 5)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex (row i)) ↔ rankFourCarrier (row i) x)
    (v w : Bits) :
    MulAut.commutingCard (parametrization i hcarrier (v,w)) =
      centralCount i (point i v w) := by
  rw [MulAut.commutingCard_eq_card_filter_of_equiv (pairEquiv.trans (parametrization i hcarrier))]
  unfold centralCount
  congr 1
  apply Finset.filter_congr
  intro n _
  let p := pair n
  change (⟨embed (point i p.1 p.2), _⟩ : smallEvenCandidate _) *
      ⟨embed (point i v w), _⟩ = ⟨embed (point i v w), _⟩ *
      ⟨embed (point i p.1 p.2), _⟩ ↔ _
  rw [Subtype.ext_iff]
  change embed (point i p.1 p.2) * embed (point i v w) =
    embed (point i v w) * embed (point i p.1 p.2) ↔ _
  simp only [embed, ← map_mul, SemidirectProduct.inl_inj]
  rfl

private theorem core_order_four (c : Core) : orderOf c = 4 ↔ c * c ≠ 1 := by
  have h4 : c ^ 4 = 1 := by
    have hh := Core.inv_mul_cancel c
    change (c * c * c) * c = 1 at hh
    simpa [pow_succ, pow_two, mul_assoc] using hh
  constructor
  · intro h hs
    have hd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hs)
    rw [h] at hd
    norm_num at hd
  · intro hs
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [pow_two] using hs) h4

private def test (i : Fin 5) (j : Fin 3) (v w : Bits) : Prop :=
  let c := point i v w
  (if i = 3 then c * c = 1 ∧ c ≠ 1 else c * c ≠ 1) ∧
    centralCount i c = (rankFourTests (row i) j).2.1

private instance (i : Fin 5) (j : Fin 3) (v w : Bits) : Decidable (test i j v w) := by
  unfold test
  infer_instance

private theorem test_eq (i : Fin 5)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex (row i)) ↔ rankFourCarrier (row i) x)
    (j : Fin 3) (v w : Bits) :
    MulAut.orderCentralizerTest (rankFourTests (row i) j)
      (parametrization i hcarrier (v,w)) ↔ test i j v w := by
  have ho : orderOf (parametrization i hcarrier (v,w)) = orderOf (point i v w) := by
    calc
      orderOf (parametrization i hcarrier (v,w)) =
          orderOf ((parametrization i hcarrier (v,w)).val) :=
        (Subgroup.orderOf_coe _).symm
      _ = orderOf (point i v w) := by
        change orderOf (SemidirectProduct.inl (point i v w)) = _
        simpa using
          (orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective
            (point i v w))
  rw [MulAut.orderCentralizerTest, ho, centralCount_eq]
  have ht : (rankFourTests (row i) j).2.2 = 0 := by fin_cases i <;> fin_cases j <;> rfl
  simp only [ht, true_or, and_true]
  unfold test
  clear ho hcarrier
  fin_cases i <;> fin_cases j <;>
    norm_num [rankFourTests, row] <;>
    simp [core_order_four, orderOf_eq_prime_iff, pow_two]


private theorem count_transfer (i : Fin 5)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex (row i)) ↔ rankFourCarrier (row i) x)
    (j : Fin 3) (v : Binary 4) :
    Nat.card {x : smallEvenCandidate (rankFourIndex (row i)) //
      rankFourMap (row i) x = v ∧ MulAut.orderCentralizerTest (rankFourTests (row i) j) x} =
      (Finset.univ.filter (test i j v.toAdd)).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  let e := parametrization i hcarrier
  refine {
    toFun := fun x => ⟨rest i x.val.val.left, ?_⟩
    invFun := fun w => ⟨e (v.toAdd, w.val), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have he : e (v.toAdd, rest i x.val.val.left) = x.val := by
      have h := e.apply_symm_apply x.val
      change e ((rankFourMap (row i) x.val).toAdd, rest i x.val.val.left) = _ at h
      rwa [x.property.1] at h
    exact (test_eq i hcarrier j _ _).mp (he.symm ▸ x.property.2)
  · exact ⟨point_coordinates i _ _, (test_eq i hcarrier j _ _).mpr w.property⟩
  · intro x
    apply Subtype.ext
    have h := e.apply_symm_apply x.val
    change e ((rankFourMap (row i) x.val).toAdd, rest i x.val.val.left) = _ at h
    simpa only [x.property.1] using h
  · intro w
    apply Subtype.ext
    exact point_rest i _ _

private def count (i : Fin 5) (j : Fin 3) (v : Binary 4) : ℕ :=
  (Finset.univ.filter (test i j v.toAdd)).card

private def fastTest (i : Fin 5) (j : Fin 3) (v w : Bits) : Prop :=
  let c := point i v w
  (if i = 3 then c * c = 1 ∧ c ≠ 1 else c * c ≠ 1) ∧
    fastCentralCount i c = (rankFourTests (row i) j).2.1

private instance (i : Fin 5) (j : Fin 3) (v w : Bits) : Decidable (fastTest i j v w) := by
  unfold fastTest
  infer_instance

private theorem fastTest_iff (i : Fin 5) (j : Fin 3) (v w : Bits) :
    fastTest i j v w ↔ test i j v w := by
  dsimp only [fastTest, test]
  rw [centralCount_fast]

private def packedCount (i : Fin 5) (j : Fin 3) (n : Fin 16) : ℕ :=
  (Finset.univ.filter (fun m : Fin 16 => fastTest i j (bits n) (bits m))).card

private theorem packedCount_eq (i : Fin 5) (j : Fin 3) (n : Fin 16) :
    packedCount i j n = count i j (Multiplicative.ofAdd (bits n)) := by
  unfold packedCount count
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (bitsEquiv.subtypeEquiv (fun m => fastTest_iff i j (bits n) (bits m)))

set_option maxHeartbeats 32000000 in
private theorem packed_count_base : ∀ (i : Fin 5) (n : Fin 16),
    packedCount i 0 n = (rankFourProfile (row i) (Multiplicative.ofAdd (bits n))).1 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem packed_count_extra : ∀ (n : Fin 16),
    packedCount 3 1 n = (rankFourProfile (row 3) (Multiplicative.ofAdd (bits n))).2.1 := by
  decide +kernel

private theorem profile_repeated : ∀ (i : Fin 5) (n : Fin 16),
    rankFourProfile (row i) (Multiplicative.ofAdd (bits n)) =
      let p := rankFourProfile (row i) (Multiplicative.ofAdd (bits n))
      (p.1, if i = 3 then p.2.1 else p.1, if i = 3 then p.2.1 else p.1) := by
  decide +kernel

private theorem packed_count (i : Fin 5) (n : Fin 16) :
    (packedCount i 0 n, packedCount i 1 n, packedCount i 2 n) =
      rankFourProfile (row i) (Multiplicative.ofAdd (bits n)) := by
  rw [profile_repeated i n]
  fin_cases i
  · exact Prod.ext (packed_count_base 0 n)
      (Prod.ext (packed_count_base 0 n) (packed_count_base 0 n))
  · exact Prod.ext (packed_count_base 1 n)
      (Prod.ext (packed_count_base 1 n) (packed_count_base 1 n))
  · exact Prod.ext (packed_count_base 2 n)
      (Prod.ext (packed_count_base 2 n) (packed_count_base 2 n))
  · exact Prod.ext (packed_count_base 3 n)
      (Prod.ext (packed_count_extra n) (packed_count_extra n))
  · exact Prod.ext (packed_count_base 4 n)
      (Prod.ext (packed_count_base 4 n) (packed_count_base 4 n))

private theorem finite_count (i : Fin 5) (v : Binary 4) :
    (count i 0 v, count i 1 v, count i 2 v) = rankFourProfile (row i) v := by
  have h := packed_count i (number v.toAdd)
  rw [packedCount_eq, packedCount_eq, packedCount_eq,
    show bits (number v.toAdd) = v.toAdd from bitsEquiv.apply_symm_apply _] at h
  exact h

/-- The intrinsic rank-four profiles for the original rows 18–22. -/
public theorem rankFourCoordinateProfile_first
    (i : Fin 7) (hi : i.val < 5)
    (hcarrier : ∀ x : SylowModel,
      x ∈ smallEvenCandidate (rankFourIndex i) ↔ rankFourCarrier i x) :
    ∀ v, rankFourCoordinateProfile i v = rankFourProfile i v := by
  let k : Fin 5 := ⟨i.val, hi⟩
  have hk : row k = i := Fin.ext rfl
  rw [← hk] at hcarrier ⊢
  intro v
  unfold rankFourCoordinateProfile
  rw [count_transfer k hcarrier 0 v, count_transfer k hcarrier 1 v,
    count_transfer k hcarrier 2 v]
  exact finite_count k v

end ReeTwo.SylowModel.SmallEvenAutB
