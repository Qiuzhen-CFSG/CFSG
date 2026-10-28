module

public import Batteries.Data.BitVec
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Tactic.FinCases
public import Theory.GroupTheory.SteinerSystem
public import Theory.Mathieu.M24.Generators

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open scoped symmDiff Pointwise

public theorem bitVec_support_card {n : Nat} (x : BitVec n) :
    (Finset.univ.filter fun i : Fin n => x.getLsb i = true).card =
      x.cpop.toNat := by
  induction x using BitVec.concat_induction with
  | nil => simp
  | concat bv b ih =>
      rw [Fin.card_filter_univ_succ']
      simp only [BitVec.getLsb_eq_getElem, BitVec.toNat_cpop_concat]
      cases b <;> simp_all [BitVec.getElem_concat_zero,
        BitVec.getElem_concat_succ]


@[reducible]
public def m24IndexChunk96 (c : Fin 7) (i : Fin 96) : Fin 759 :=
  ⟨c.val * 96 + i.val, by omega⟩

@[reducible]
public def m24IndexChunk87 (i : Fin 87) : Fin 759 :=
  ⟨672 + i.val, by omega⟩

public theorem m24ForallFin759_of_chunks {P : Fin 759 → Prop}
    (h0 : ∀ i : Fin 96, P (m24IndexChunk96 0 i))
    (h1 : ∀ i : Fin 96, P (m24IndexChunk96 1 i))
    (h2 : ∀ i : Fin 96, P (m24IndexChunk96 2 i))
    (h3 : ∀ i : Fin 96, P (m24IndexChunk96 3 i))
    (h4 : ∀ i : Fin 96, P (m24IndexChunk96 4 i))
    (h5 : ∀ i : Fin 96, P (m24IndexChunk96 5 i))
    (h6 : ∀ i : Fin 96, P (m24IndexChunk96 6 i))
    (h7 : ∀ i : Fin 87, P (m24IndexChunk87 i)) : ∀ i, P i := by
  have ofChunk96 (c : Fin 7)
      (hcore : ∀ j : Fin 96, P (m24IndexChunk96 c j))
      (i : Fin 759) (hlo : c.val * 96 ≤ i.val)
      (hhi : i.val < (c.val + 1) * 96) : P i := by
    let j : Fin 96 := ⟨i.val - c.val * 96, by omega⟩
    have hj : m24IndexChunk96 c j = i := by
      apply Fin.ext
      simp [j]
      omega
    simpa only [hj] using hcore j
  intro i
  by_cases hi0 : i.val < 96
  · exact ofChunk96 0 h0 i (by omega) hi0
  by_cases hi1 : i.val < 192
  · exact ofChunk96 1 h1 i (by omega) hi1
  by_cases hi2 : i.val < 288
  · exact ofChunk96 2 h2 i (by omega) hi2
  by_cases hi3 : i.val < 384
  · exact ofChunk96 3 h3 i (by omega) hi3
  by_cases hi4 : i.val < 480
  · exact ofChunk96 4 h4 i (by omega) hi4
  by_cases hi5 : i.val < 576
  · exact ofChunk96 5 h5 i (by omega) hi5
  by_cases hi6 : i.val < 672
  · exact ofChunk96 6 h6 i (by omega) hi6
  · let j : Fin 87 := ⟨i.val - 672, by omega⟩
    have hj : m24IndexChunk87 j = i := by
      apply Fin.ext
      simp [j]
      omega
    simpa only [hj] using h7 j


/-!
# A finite certificate for the extended binary Golay code

The twelve rows below are a systematic basis for the 12-dimensional binary
code spanned by the 759 Atlas octads.  Later modules check the minimum weight
from doubly-even and column-pair invariants and identify every explicit octad
with a weight-eight codeword.
-/

@[expose] public def m24GolayRow : Fin 12 -> BitVec 24
  | 0 => BitVec.ofNat 24 11718657
  | 1 => BitVec.ofNat 24 15369218
  | 2 => BitVec.ofNat 24 12997636
  | 3 => BitVec.ofNat 24 6226952
  | 4 => BitVec.ofNat 24 775184
  | 5 => BitVec.ofNat 24 11485216
  | 6 => BitVec.ofNat 24 16519232
  | 7 => BitVec.ofNat 24 13735040
  | 8 => BitVec.ofNat 24 10274048
  | 9 => BitVec.ofNat 24 3495424
  | 10 => BitVec.ofNat 24 6789120
  | 11 => BitVec.ofNat 24 7987200

@[expose] public def m24GolaySelect (b : Bool) (x : BitVec 24) : BitVec 24 :=
  if b then x else 0

private theorem m24GolaySelect_xor (a b : Bool) (x : BitVec 24) :
    m24GolaySelect (a ^^ b) x =
      m24GolaySelect a x ^^^ m24GolaySelect b x := by
  cases a <;> cases b <;> simp [m24GolaySelect]

private theorem m24GolaySelect_getLsbD (b : Bool) (x : BitVec 24) (i : Nat) :
    (m24GolaySelect b x).getLsbD i = (b && x.getLsbD i) := by
  cases b <;> simp [m24GolaySelect]

private theorem m24Golay_getLsb_xor (x y : BitVec 24) (i : Fin 24) :
    (x ^^^ y).getLsb i = (x.getLsb i ^^ y.getLsb i) := by
  simp

/-- The 24-bit Golay word encoded by a 12-bit message. -/
@[expose] public def m24GolayCode (u : Fin 4096) : BitVec 24 :=
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 0) (m24GolayRow 0) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 1) (m24GolayRow 1) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 2) (m24GolayRow 2) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 3) (m24GolayRow 3) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 4) (m24GolayRow 4) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 5) (m24GolayRow 5) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 6) (m24GolayRow 6) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 7) (m24GolayRow 7) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 8) (m24GolayRow 8) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 9) (m24GolayRow 9) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 10) (m24GolayRow 10) ^^^
  m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD 11) (m24GolayRow 11)

/-- Addition of Golay messages, represented by bitwise xor. -/
@[expose] public def m24GolayMessageXor (u v : Fin 4096) : Fin 4096 :=
  (BitVec.ofFin (w := 12) u ^^^ BitVec.ofFin (w := 12) v).toFin

public theorem m24GolayCode_xor (u v : Fin 4096) :
    m24GolayCode (m24GolayMessageXor u v) =
      m24GolayCode u ^^^ m24GolayCode v := by
  simp only [m24GolayCode, m24GolayMessageXor, BitVec.ofFin_toFin,
    BitVec.getLsbD_xor, m24GolaySelect_xor]
  ac_rfl

@[reducible]
private def m24GolayPivot : Fin 12 -> Fin 24
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 11
  | 11 => 13

private theorem m24GolayCode_pivot (u : Fin 4096) (i : Fin 12) :
    (m24GolayCode u).getLsbD (m24GolayPivot i) =
      (BitVec.ofFin (w := 12) u).getLsbD i := by
  simp only [m24GolayCode, BitVec.getLsbD_xor, m24GolaySelect_getLsbD]
  fin_cases i <;> simp [m24GolayRow, m24GolayPivot]

/-- The support of a Golay codeword. -/
@[expose] public def m24GolayWord (u : Fin 4096) : Finset (Fin 24) :=
  Finset.univ.filter fun x => (m24GolayCode u).getLsb x = true

/-- Xor of messages becomes symmetric difference of supports. -/
public theorem m24GolayWord_symmDiff (u v : Fin 4096) :
    m24GolayWord (m24GolayMessageXor u v) =
      m24GolayWord u ∆ m24GolayWord v := by
  ext x
  simp only [m24GolayWord, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [m24GolayCode_xor, m24Golay_getLsb_xor]
  simp only [Finset.mem_symmDiff]
  cases huBit : (m24GolayCode u)[x.val] <;>
    cases hvBit : (m24GolayCode v)[x.val] <;> simp [huBit, hvBit]

/-- The systematic Golay encoding is injective. -/
public theorem m24GolayWord_injective : Function.Injective m24GolayWord := by
  intro u v huv
  have hBits : BitVec.ofFin (w := 12) u = BitVec.ofFin (w := 12) v := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let i : Fin 12 := ⟨k, hk⟩
    change (BitVec.ofFin (w := 12) u).getLsbD i.val =
      (BitVec.ofFin (w := 12) v).getLsbD i.val
    rw [← m24GolayCode_pivot u i, ← m24GolayCode_pivot v i]
    have hm := Finset.ext_iff.mp huv (m24GolayPivot i)
    simp only [m24GolayWord, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    cases huBit : (m24GolayCode u)[(m24GolayPivot i).val] <;>
      cases hvBit : (m24GolayCode v)[(m24GolayPivot i).val] <;> simp_all
  exact congrArg BitVec.toFin hBits

public theorem m24GolayMessageXor_ne_zero {u v : Fin 4096} (huv : u ≠ v) :
    m24GolayMessageXor u v ≠ 0 := by
  intro hzero
  have hBitVec : BitVec.ofFin (w := 12) u ^^^ BitVec.ofFin (w := 12) v = 0 := by
    apply BitVec.toFin_injective
    simpa [m24GolayMessageXor] using hzero
  have huvBit : BitVec.ofFin (w := 12) u = BitVec.ofFin (w := 12) v := by
    rw [xor_eq_iff_left_eq, zero_xor] at hBitVec
    exact hBitVec
  apply huv
  exact congrArg BitVec.toFin huvBit

/-- Two weight-eight codewords with nonzero difference meet in at most four points. -/
public theorem m24Golay_inter_lt_five (u v : Fin 4096)
    (hu : (m24GolayWord u).card = 8) (hv : (m24GolayWord v).card = 8)
    (hmin : 8 ≤ (m24GolayWord (m24GolayMessageXor u v)).card) :
    (m24GolayWord u ∩ m24GolayWord v).card < 5 := by
  rw [m24GolayWord_symmDiff, Finset.symmDiff_def] at hmin
  have hdisj : Disjoint (m24GolayWord u \ m24GolayWord v)
      (m24GolayWord v \ m24GolayWord u) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_sdiff] at ha hb
    exact ha.2 hb.1
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_sdiff, Finset.card_sdiff, hu, hv] at hmin
  rw [Finset.inter_comm (m24GolayWord v) (m24GolayWord u)] at hmin
  omega

/-! Structural certificates for the Golay code's minimum weight. -/

private theorem m24GolaySelect_ofNat (b : Bool) (n : Nat) :
    m24GolaySelect b (BitVec.ofNat 24 n) =
      BitVec.ofNat 24 (if b then n else 0) := by
  cases b <;> rfl

/-- The contribution of message bits zero through three to the Golay encoder. -/
@[reducible]
public def m24GolayNibble0 (i : Fin 16) : Nat :=
  match i.val with
  | 0 => 0 | 1 => 11718657 | 2 => 15369218 | 3 => 5788675
  | 4 => 12997636 | 5 => 7635973 | 6 => 2936838 | 7 => 10354695
  | 8 => 6226952 | 9 => 15586313 | 10 => 11894794 | 11 => 479243
  | 12 => 10047500 | 13 => 2850829 | 14 => 7590926 | 15 => 12649487
  | _ => 0

/-- The contribution of message bits four through seven to the Golay encoder. -/
@[reducible]
public def m24GolayNibble1 (i : Fin 16) : Nat :=
  match i.val with
  | 0 => 0 | 1 => 775184 | 2 => 11485216 | 3 => 10785840
  | 4 => 16519232 | 5 => 16237648 | 6 => 5460064 | 7 => 5801072
  | 8 => 13735040 | 9 => 14303376 | 10 => 8311968 | 11 => 7667888
  | 12 => 2983104 | 13 => 2511056 | 14 => 8570080 | 15 => 8982768
  | _ => 0

/-- The contribution of message bits eight through eleven to the Golay encoder. -/
@[reducible]
public def m24GolayNibble2 (i : Fin 16) : Nat :=
  match i.val with
  | 0 => 0 | 1 => 10274048 | 2 => 3495424 | 3 => 11113216
  | 4 => 6789120 | 5 => 16473344 | 6 => 5426688 | 7 => 13503232
  | 8 => 7987200 | 9 => 15017216 | 10 => 5027328 | 11 => 13660928
  | 12 => 1996800 | 13 => 8568064 | 14 => 2829824 | 15 => 12053248
  | _ => 0

private theorem m24GolayNibble0_spec :
    ∀ i : Fin 16, m24GolayNibble0 i =
      (if i.val.testBit 0 then 11718657 else 0) ^^^
      (if i.val.testBit 1 then 15369218 else 0) ^^^
      (if i.val.testBit 2 then 12997636 else 0) ^^^
      (if i.val.testBit 3 then 6226952 else 0) := by
  decide +kernel

private theorem m24GolayNibble1_spec :
    ∀ i : Fin 16, m24GolayNibble1 i =
      (if i.val.testBit 0 then 775184 else 0) ^^^
      (if i.val.testBit 1 then 11485216 else 0) ^^^
      (if i.val.testBit 2 then 16519232 else 0) ^^^
      (if i.val.testBit 3 then 13735040 else 0) := by
  decide +kernel

private theorem m24GolayNibble2_spec :
    ∀ i : Fin 16, m24GolayNibble2 i =
      (if i.val.testBit 0 then 10274048 else 0) ^^^
      (if i.val.testBit 1 then 3495424 else 0) ^^^
      (if i.val.testBit 2 then 6789120 else 0) ^^^
      (if i.val.testBit 3 then 7987200 else 0) := by
  decide +kernel

@[reducible]
public def m24GolayNibbleIndex0 (u : Fin 4096) : Fin 16 :=
  ⟨u.val % 16, by omega⟩

@[reducible]
public def m24GolayNibbleIndex1 (u : Fin 4096) : Fin 16 :=
  ⟨u.val / 16 % 16, by omega⟩

@[reducible]
public def m24GolayNibbleIndex2 (u : Fin 4096) : Fin 16 :=
  ⟨u.val / 256, by omega⟩

private theorem m24GolayNibbleIndex0_testBit (u : Fin 4096) (i : Nat)
    (hi : i < 4) :
    (m24GolayNibbleIndex0 u).val.testBit i = u.val.testBit i := by
  change (u.val % 16).testBit i = u.val.testBit i
  simpa [show 16 = 2 ^ 4 by decide +kernel, hi] using
    Nat.testBit_mod_two_pow u.val 4 i

private theorem m24GolayNibbleIndex1_testBit (u : Fin 4096) (i : Nat)
    (hi : i < 4) :
    (m24GolayNibbleIndex1 u).val.testBit i = u.val.testBit (i + 4) := by
  change (u.val / 16 % 16).testBit i = u.val.testBit (i + 4)
  rw [show 16 = 2 ^ 4 by decide +kernel]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  exact Nat.testBit_div_two_pow u.val i

private theorem m24GolayNibbleIndex2_testBit (u : Fin 4096) (i : Nat) :
    (m24GolayNibbleIndex2 u).val.testBit i = u.val.testBit (i + 8) := by
  change (u.val / 256).testBit i = u.val.testBit (i + 8)
  rw [show 256 = 2 ^ 8 by decide +kernel]
  exact Nat.testBit_div_two_pow u.val i

/-- A compact three-table implementation of the same systematic Golay encoder. -/
@[reducible, expose] public def m24GolayMask (u : Fin 4096) : Nat :=
  m24GolayNibble0 (m24GolayNibbleIndex0 u) ^^^
  m24GolayNibble1 (m24GolayNibbleIndex1 u) ^^^
  m24GolayNibble2 (m24GolayNibbleIndex2 u)

public theorem m24GolayCode_eq_ofNat_mask (u : Fin 4096) :
    m24GolayCode u = BitVec.ofNat 24 (m24GolayMask u) := by
  rw [m24GolayMask, m24GolayNibble0_spec, m24GolayNibble1_spec,
    m24GolayNibble2_spec]
  rw [m24GolayNibbleIndex0_testBit u 0 (by omega),
    m24GolayNibbleIndex0_testBit u 1 (by omega),
    m24GolayNibbleIndex0_testBit u 2 (by omega),
    m24GolayNibbleIndex0_testBit u 3 (by omega)]
  rw [m24GolayNibbleIndex1_testBit u 0 (by omega),
    m24GolayNibbleIndex1_testBit u 1 (by omega),
    m24GolayNibbleIndex1_testBit u 2 (by omega),
    m24GolayNibbleIndex1_testBit u 3 (by omega)]
  rw [m24GolayNibbleIndex2_testBit u 0, m24GolayNibbleIndex2_testBit u 1,
    m24GolayNibbleIndex2_testBit u 2, m24GolayNibbleIndex2_testBit u 3]
  simp only [Nat.reduceAdd]
  simp only [m24GolayCode, m24GolayRow, BitVec.getLsbD_ofFin,
    m24GolaySelect_ofNat, ← BitVec.ofNat_xor]
  congr 1
  ac_rfl

@[reducible]
private def m24BitVecSupport (x : BitVec 24) : Finset (Fin 24) :=
  Finset.univ.filter fun i => x.getLsb i = true

private theorem m24BitVecSupport_xor (x y : BitVec 24) :
    m24BitVecSupport (x ^^^ y) =
      m24BitVecSupport x ∆ m24BitVecSupport y := by
  ext i
  simp only [m24BitVecSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  rw [m24Golay_getLsb_xor]
  cases x.getLsb i <;> cases y.getLsb i <;> simp

private theorem m24_card_symmDiff_add_twice_inter
    (s t : Finset (Fin 24)) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have hdisj : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_sdiff] at ha hb
    exact ha.2 hb.1
  have hs := Finset.card_sdiff_add_card_inter s t
  have ht := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at ht
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  omega

private theorem m24_two_dvd_card_symmDiff
    {s t : Finset (Fin 24)} (hs : 2 ∣ s.card) (ht : 2 ∣ t.card) :
    2 ∣ (s ∆ t).card := by
  rcases hs with ⟨a, ha⟩
  rcases ht with ⟨b, hb⟩
  have hcard := m24_card_symmDiff_add_twice_inter s t
  refine ⟨a + b - (s ∩ t).card, ?_⟩
  omega

private theorem m24_four_dvd_card_symmDiff
    {s t : Finset (Fin 24)} (hs : 4 ∣ s.card) (ht : 4 ∣ t.card)
    (hst : 2 ∣ (s ∩ t).card) : 4 ∣ (s ∆ t).card := by
  rcases hs with ⟨a, ha⟩
  rcases ht with ⟨b, hb⟩
  rcases hst with ⟨c, hc⟩
  have hcard := m24_card_symmDiff_add_twice_inter s t
  refine ⟨a + b - c, ?_⟩
  omega

private def m24GolayCodeInvariant (x : BitVec 24) : Prop :=
  4 ∣ (m24BitVecSupport x).card ∧
    ∀ i : Fin 12,
      2 ∣ (m24BitVecSupport x ∩
        m24BitVecSupport (m24GolayRow i)).card

private theorem m24GolayRow_doublyEven :
    ∀ i : Fin 12, 4 ∣ (m24BitVecSupport (m24GolayRow i)).card := by
  decide +kernel

private theorem m24GolayRow_orthogonal :
    ∀ i j : Fin 12,
      2 ∣ (m24BitVecSupport (m24GolayRow i) ∩
        m24BitVecSupport (m24GolayRow j)).card := by
  decide +kernel

private theorem m24GolayCodeInvariant_zero : m24GolayCodeInvariant 0 := by
  constructor
  · simp [m24BitVecSupport]
  · intro i
    simp [m24BitVecSupport]

private theorem m24GolayCodeInvariant_xor_select
    (x : BitVec 24) (hx : m24GolayCodeInvariant x)
    (b : Bool) (i : Fin 12) :
    m24GolayCodeInvariant (x ^^^ m24GolaySelect b (m24GolayRow i)) := by
  cases b
  · simpa [m24GolaySelect] using hx
  · constructor
    · rw [m24GolaySelect, if_pos rfl, m24BitVecSupport_xor]
      exact m24_four_dvd_card_symmDiff hx.1
        (m24GolayRow_doublyEven i) (hx.2 i)
    · intro j
      rw [m24GolaySelect, if_pos rfl, m24BitVecSupport_xor]
      rw [show
        (m24BitVecSupport x ∆ m24BitVecSupport (m24GolayRow i)) ∩
            m24BitVecSupport (m24GolayRow j) =
          (m24BitVecSupport x ∩ m24BitVecSupport (m24GolayRow j)) ∆
            (m24BitVecSupport (m24GolayRow i) ∩
              m24BitVecSupport (m24GolayRow j)) by
        ext a
        simp only [Finset.mem_inter, Finset.mem_symmDiff]
        tauto]
      exact m24_two_dvd_card_symmDiff (hx.2 j)
        (m24GolayRow_orthogonal i j)

private def m24GolayCodePrefix (u : Fin 4096) : Nat → BitVec 24
  | 0 => 0
  | n + 1 =>
      if h : n < 12 then
        m24GolayCodePrefix u n ^^^
          m24GolaySelect ((BitVec.ofFin (w := 12) u).getLsbD n)
            (m24GolayRow ⟨n, h⟩)
      else
        m24GolayCodePrefix u n

private theorem m24GolayCodePrefix_invariant (u : Fin 4096) :
    ∀ n, m24GolayCodeInvariant (m24GolayCodePrefix u n) := by
  intro n
  induction n with
  | zero => exact m24GolayCodeInvariant_zero
  | succ n ih =>
      rw [m24GolayCodePrefix]
      split
      · exact m24GolayCodeInvariant_xor_select _ ih _ _
      · exact ih

private theorem m24GolayCode_invariant (u : Fin 4096) :
    m24GolayCodeInvariant (m24GolayCode u) := by
  rw [← show m24GolayCodePrefix u 12 = m24GolayCode u by
    simp [m24GolayCodePrefix, m24GolayCode]]
  exact m24GolayCodePrefix_invariant u 12

@[reducible]
private def m24GolayColumn (x : Fin 24) : BitVec 12 :=
  BitVec.ofFnLE fun i => (m24GolayRow i).getLsb x

@[reducible]
private def m24GolayPairDecode (s : BitVec 12) : Nat :=
  match s.toNat with
  | 3 => 1
  | 5 => 2
  | 6 => 26
  | 9 => 3
  | 10 => 27
  | 12 => 51
  | 17 => 4
  | 18 => 28
  | 20 => 52
  | 24 => 76
  | 33 => 5
  | 34 => 29
  | 36 => 53
  | 40 => 77
  | 48 => 101
  | 63 => 281
  | 65 => 6
  | 66 => 30
  | 68 => 54
  | 72 => 78
  | 80 => 102
  | 96 => 126
  | 129 => 7
  | 130 => 31
  | 132 => 55
  | 136 => 79
  | 144 => 103
  | 160 => 127
  | 192 => 151
  | 219 => 405
  | 231 => 215
  | 252 => 356
  | 257 => 8
  | 258 => 32
  | 260 => 56
  | 264 => 80
  | 272 => 104
  | 288 => 128
  | 320 => 152
  | 349 => 382
  | 359 => 191
  | 378 => 331
  | 384 => 176
  | 414 => 226
  | 423 => 167
  | 441 => 306
  | 455 => 143
  | 483 => 71
  | 485 => 47
  | 486 => 23
  | 495 => 95
  | 503 => 119
  | 513 => 9
  | 514 => 33
  | 516 => 57
  | 520 => 81
  | 528 => 105
  | 544 => 129
  | 576 => 153
  | 591 => 355
  | 630 => 406
  | 633 => 263
  | 640 => 177
  | 670 => 202
  | 685 => 526
  | 691 => 476
  | 725 => 276
  | 746 => 305
  | 768 => 201
  | 798 => 178
  | 811 => 376
  | 821 => 326
  | 851 => 426
  | 876 => 282
  | 910 => 106
  | 918 => 82
  | 922 => 58
  | 924 => 34
  | 927 => 10
  | 958 => 130
  | 969 => 332
  | 990 => 154
  | 999 => 239
  | 1008 => 381
  | 1025 => 11
  | 1026 => 35
  | 1028 => 59
  | 1032 => 83
  | 1040 => 107
  | 1055 => 137
  | 1056 => 131
  | 1071 => 113
  | 1079 => 89
  | 1083 => 65
  | 1085 => 41
  | 1086 => 17
  | 1088 => 155
  | 1151 => 161
  | 1152 => 179
  | 1215 => 185
  | 1230 => 334
  | 1237 => 228
  | 1257 => 379
  | 1266 => 258
  | 1280 => 203
  | 1343 => 209
  | 1355 => 252
  | 1366 => 357
  | 1388 => 234
  | 1393 => 404
  | 1421 => 352
  | 1427 => 327
  | 1450 => 501
  | 1460 => 478
  | 1496 => 431
  | 1511 => 287
  | 1536 => 227
  | 1599 => 233
  | 1621 => 180
  | 1626 => 380
  | 1635 => 333
  | 1644 => 210
  | 1675 => 455
  | 1685 => 156
  | 1702 => 351
  | 1720 => 328
  | 1733 => 108
  | 1745 => 60
  | 1748 => 12
  | 1751 => 36
  | 1757 => 84
  | 1781 => 132
  | 1799 => 502
  | 1817 => 477
  | 1836 => 162
  | 1842 => 311
  | 1868 => 138
  | 1892 => 90
  | 1896 => 66
  | 1901 => 18
  | 1902 => 42
  | 1916 => 114
  | 1950 => 251
  | 1953 => 257
  | 1986 => 403
  | 2005 => 204
  | 2028 => 186
  | 2043 => 358
  | 2049 => 13
  | 2050 => 37
  | 2052 => 61
  | 2056 => 85
  | 2064 => 109
  | 2080 => 133
  | 2112 => 157
  | 2135 => 260
  | 2157 => 304
  | 2170 => 211
  | 2176 => 181
  | 2205 => 479
  | 2219 => 254
  | 2230 => 309
  | 2254 => 286
  | 2289 => 430
  | 2304 => 205
  | 2319 => 453
  | 2357 => 230
  | 2362 => 163
  | 2394 => 139
  | 2410 => 115
  | 2418 => 91
  | 2424 => 43
  | 2427 => 19
  | 2430 => 67
  | 2451 => 279
  | 2476 => 377
  | 2505 => 236
  | 2516 => 402
  | 2535 => 335
  | 2554 => 187
  | 2560 => 229
  | 2587 => 310
  | 2606 => 503
  | 2613 => 206
  | 2652 => 429
  | 2659 => 285
  | 2695 => 401
  | 2744 => 280
  | 2761 => 212
  | 2770 => 359
  | 2788 => 259
  | 2815 => 378
  | 2837 => 134
  | 2853 => 110
  | 2865 => 62
  | 2868 => 14
  | 2871 => 38
  | 2877 => 86
  | 2886 => 303
  | 2889 => 188
  | 2933 => 158
  | 2938 => 235
  | 2953 => 164
  | 2974 => 253
  | 2978 => 454
  | 2997 => 182
  | 3009 => 92
  | 3016 => 20
  | 3019 => 44
  | 3021 => 68
  | 3033 => 116
  | 3049 => 140
  | 3072 => 277
  | 3135 => 329
  | 3150 => 190
  | 3161 => 354
  | 3171 => 237
  | 3188 => 383
  | 3214 => 166
  | 3219 => 207
  | 3237 => 452
  | 3256 => 232
  | 3270 => 94
  | 3274 => 70
  | 3276 => 46
  | 3279 => 22
  | 3294 => 118
  | 3310 => 142
  | 3347 => 183
  | 3356 => 308
  | 3366 => 256
  | 3369 => 551
  | 3397 => 427
  | 3450 => 283
  | 3459 => 111
  | 3473 => 39
  | 3474 => 15
  | 3479 => 63
  | 3483 => 87
  | 3507 => 135
  | 3534 => 214
  | 3539 => 159
  | 3552 => 302
  | 3581 => 261
  | 3597 => 255
  | 3606 => 451
  | 3619 => 165
  | 3640 => 184
  | 3651 => 141
  | 3681 => 45
  | 3682 => 21
  | 3687 => 69
  | 3691 => 93
  | 3699 => 117
  | 3736 => 136
  | 3752 => 112
  | 3760 => 88
  | 3769 => 16
  | 3770 => 40
  | 3772 => 64
  | 3790 => 238
  | 3797 => 301
  | 3811 => 189
  | 3832 => 160
  | 3850 => 353
  | 3893 => 278
  | 3920 => 262
  | 3935 => 407
  | 3939 => 213
  | 3948 => 330
  | 3972 => 527
  | 3987 => 231
  | 4015 => 307
  | 4024 => 208
  | 4041 => 284
  | 4086 => 428
  | _ => 576

private theorem m24GolayPairDecode_spec :
    ∀ a b : Fin 24, a < b →
      m24GolayPairDecode (m24GolayColumn a ^^^ m24GolayColumn b) =
        a.val * 24 + b.val := by
  decide +kernel

private theorem m24GolayColumn_pair_eq_of_lt
    {a b c d : Fin 24} (hab : a < b) (hcd : c < d)
    (hpair : m24GolayColumn a ^^^ m24GolayColumn b =
      m24GolayColumn c ^^^ m24GolayColumn d) :
    a = c ∧ b = d := by
  have hcode := congrArg m24GolayPairDecode hpair
  rw [m24GolayPairDecode_spec a b hab,
    m24GolayPairDecode_spec c d hcd] at hcode
  have ha : a.val = c.val := by omega
  have hb : b.val = d.val := by omega
  exact ⟨Fin.ext ha, Fin.ext hb⟩

private theorem m24Golay_four_columns_xor_eq_zero
    (x y z w : Fin 24)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (horth : ∀ i : Fin 12,
      2 ∣ (({x, y, z, w} : Finset (Fin 24)) ∩
        m24BitVecSupport (m24GolayRow i)).card) :
    (m24GolayColumn x ^^^ m24GolayColumn y) ^^^
      (m24GolayColumn z ^^^ m24GolayColumn w) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 12 := ⟨k, hk⟩
  have hi := horth i
  have hinter :
      ({x, y, z, w} : Finset (Fin 24)) ∩
          m24BitVecSupport (m24GolayRow i) =
        ({x, y, z, w} : Finset (Fin 24)).filter
          (fun a => (m24GolayRow i).getLsb a = true) := by
    ext a
    simp [m24BitVecSupport]
  rw [hinter] at hi
  by_cases hxi : (m24GolayRow ⟨k, hk⟩).toNat.testBit x.val = true
  all_goals by_cases hyi : (m24GolayRow ⟨k, hk⟩).toNat.testBit y.val = true
  all_goals by_cases hzi : (m24GolayRow ⟨k, hk⟩).toNat.testBit z.val = true
  all_goals by_cases hwi : (m24GolayRow ⟨k, hk⟩).toNat.testBit w.val = true
  all_goals
    simp [Finset.filter_insert, Finset.filter_singleton, BitVec.getLsb, i,
      hxy, hxz, hxw, hyz, hyw, hzw, hxi, hyi, hzi, hwi] at hi
  all_goals
    simp [m24GolayColumn, hk, BitVec.getLsb, hxi, hyi, hzi, hwi]

private theorem m24GolayWord_card_ne_four (u : Fin 4096) :
    (m24GolayWord u).card ≠ 4 := by
  intro hcard
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hword⟩ :=
    Finset.card_eq_four.mp hcard
  have horth : ∀ i : Fin 12,
      2 ∣ (({x, y, z, w} : Finset (Fin 24)) ∩
        m24BitVecSupport (m24GolayRow i)).card := by
    intro i
    have hi := (m24GolayCode_invariant u).2 i
    change 2 ∣ (m24GolayWord u ∩
      m24BitVecSupport (m24GolayRow i)).card at hi
    simpa only [hword] using hi
  have hzero := m24Golay_four_columns_xor_eq_zero x y z w
    hxy hxz hxw hyz hyw hzw horth
  have hpairs : m24GolayColumn x ^^^ m24GolayColumn y =
      m24GolayColumn z ^^^ m24GolayColumn w := by
    exact (xor_eq_iff_left_eq _ _ _).mp hzero |>.trans (zero_xor _)
  by_cases hxylt : x < y
  · by_cases hzwlt : z < w
    · exact hxz (m24GolayColumn_pair_eq_of_lt hxylt hzwlt hpairs).1
    · have hwz : w < z :=
        lt_of_le_of_ne (le_of_not_gt hzwlt) hzw.symm
      have hpairs' : m24GolayColumn x ^^^ m24GolayColumn y =
          m24GolayColumn w ^^^ m24GolayColumn z := by
        exact hpairs.trans (LawfulXor.xor_comm _ _)
      exact hxw (m24GolayColumn_pair_eq_of_lt hxylt hwz hpairs').1
  · have hyx : y < x :=
      lt_of_le_of_ne (le_of_not_gt hxylt) hxy.symm
    by_cases hzwlt : z < w
    · have hpairs' : m24GolayColumn y ^^^ m24GolayColumn x =
          m24GolayColumn z ^^^ m24GolayColumn w := by
        calc
          m24GolayColumn y ^^^ m24GolayColumn x =
              m24GolayColumn x ^^^ m24GolayColumn y :=
            LawfulXor.xor_comm _ _
          _ = m24GolayColumn z ^^^ m24GolayColumn w := hpairs
      exact hyz (m24GolayColumn_pair_eq_of_lt hyx hzwlt hpairs').1
    · have hwz : w < z :=
        lt_of_le_of_ne (le_of_not_gt hzwlt) hzw.symm
      have hpairs' : m24GolayColumn y ^^^ m24GolayColumn x =
          m24GolayColumn w ^^^ m24GolayColumn z := by
        calc
          m24GolayColumn y ^^^ m24GolayColumn x =
              m24GolayColumn x ^^^ m24GolayColumn y :=
            LawfulXor.xor_comm _ _
          _ = m24GolayColumn z ^^^ m24GolayColumn w := hpairs
          _ = m24GolayColumn w ^^^ m24GolayColumn z :=
            LawfulXor.xor_comm _ _
      exact hyw (m24GolayColumn_pair_eq_of_lt hyx hwz hpairs').1

/-- Every nonzero word of the certified extended Golay code has weight at least eight. -/
public theorem m24Golay_minWeight
    (u : Fin 4096) (hu : u ≠ 0) :
    8 ≤ (m24GolayWord u).card := by
  have hdvd := (m24GolayCode_invariant u).1
  change 4 ∣ (m24GolayWord u).card at hdvd
  have hne : m24GolayWord u ≠ ∅ := by
    intro hempty
    apply hu
    apply m24GolayWord_injective
    rw [hempty]
    simp [m24GolayWord, m24GolayCode, m24GolaySelect]
  have hpos : 0 < (m24GolayWord u).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hneFour := m24GolayWord_card_ne_four u
  rcases hdvd with ⟨k, hk⟩
  omega

/-!
# Reflected messages for the explicit W24 octads

The reflected message table below identifies each of the 759 Atlas octads with
one weight-eight word in the certified 12-dimensional extended binary Golay
code.  This turns the code minimum-weight theorem into the pairwise
intersection bound needed for the Steiner system.
-/

@[expose] public def m24ChunkMessage0 : Array (Fin 4096) := #[
  1087, 94, 926, 2078, 30, 110, 174, 302, 2606, 3278, 334, 591,
  143, 142, 1294, 2319, 1550, 526, 1038, 2062, 15, 630, 2230, 310,
  54, 214, 1366, 2135, 1174, 151, 279, 2326, 3606, 534, 535, 1046,
  22, 487, 1126, 2150, 1702, 166, 806, 3366, 551, 1062, 38, 2087,
  39, 710, 198, 2886, 326, 1606, 1095, 71, 2118, 70, 1414, 2438,
  390, 646, 2695, 1159, 2182, 1799, 774, 262, 263, 2566, 518, 3079,
  3078, 1030, 2054, 6, 7, 2426, 186, 570, 58, 219, 1626, 90,
  1178, 2202, 1306, 282, 283, 2587, 538, 3098, 27, 746, 1130, 107,
]

@[expose] public def m24ChunkMessage1 : Array (Fin 4096) := #[
  1450, 2219, 811, 298, 1578, 3114, 43, 2090, 42, 458, 202, 842,
  1355, 2634, 1098, 2122, 74, 2123, 2442, 395, 1675, 2698, 650, 1162,
  138, 3850, 778, 2314, 266, 522, 523, 1034, 3083, 1035, 11, 2058,
  10, 1266, 115, 114, 434, 691, 1842, 307, 2610, 3122, 1074, 50,
  2099, 466, 2770, 851, 338, 594, 3154, 1107, 2130, 82, 3475, 402,
  1682, 658, 147, 2194, 146, 2834, 786, 1298, 2322, 1555, 530, 1043,
  1042, 2066, 18, 2067, 19, 2274, 226, 866, 1378, 354, 3683, 610,
  2146, 99, 2978, 418, 674, 1187, 3234, 162, 163, 1315, 2339, 2338,
]

@[expose] public def m24ChunkMessage2 : Array (Fin 4096) := #[
  290, 1570, 2594, 546, 547, 1058, 1059, 2082, 34, 1986, 2498, 707,
  1218, 1219, 2243, 194, 3394, 322, 2371, 323, 1602, 579, 2626, 578,
  3138, 1090, 66, 67, 899, 898, 1410, 387, 3714, 642, 3202, 1154,
  2178, 130, 2179, 131, 1794, 770, 2819, 3330, 1282, 1283, 259, 2306,
  258, 1539, 3586, 1538, 2562, 2563, 515, 1026, 3075, 2051, 3, 2050,
  2, 252, 316, 572, 2108, 349, 2652, 1116, 1180, 156, 2205, 3356,
  284, 1564, 541, 29, 28, 1900, 2157, 108, 2476, 685, 1196, 301,
  556, 3116, 1068, 44, 45, 460, 716, 205, 2380, 588, 1100, 1101,
]

@[expose] public def m24ChunkMessage3 : Array (Fin 4096) := #[
  2124, 76, 1421, 396, 1676, 2700, 2188, 140, 781, 2828, 780, 1292,
  268, 3597, 524, 1037, 3084, 2060, 12, 2061, 13, 372, 3188, 117,
  1460, 692, 181, 2869, 1588, 1076, 53, 2100, 52, 2516, 1749, 212,
  852, 596, 1108, 2132, 84, 85, 404, 405, 2708, 660, 3220, 148,
  1812, 788, 1301, 2324, 276, 2580, 533, 1044, 3093, 1045, 2069, 2068,
  20, 2788, 1252, 228, 2404, 356, 612, 613, 1125, 100, 932, 420,
  3237, 165, 2212, 164, 804, 1317, 1316, 2340, 293, 3620, 1573, 2596,
  548, 1060, 2084, 36, 2085, 964, 1476, 1220, 2244, 2245, 197, 837,
]

@[expose] public def m24ChunkMessage4 : Array (Fin 4096) := #[
  1348, 3397, 325, 324, 3652, 1604, 580, 2629, 3140, 69, 2116, 68,
  3972, 901, 2437, 388, 1668, 644, 645, 3204, 1156, 1157, 133, 2180,
  132, 1796, 2820, 3332, 1284, 2308, 260, 2309, 261, 1540, 1541, 2565,
  517, 2564, 516, 1029, 3076, 1028, 4, 2053, 5, 633, 1144, 120,
  441, 3768, 184, 824, 1336, 1080, 2104, 2105, 57, 1496, 728, 2264,
  856, 344, 3161, 89, 2136, 88, 2456, 408, 664, 665, 1177, 152,
  1817, 2840, 280, 2329, 1560, 2584, 536, 1049, 3096, 1048, 2072, 24,
  25, 488, 1257, 2280, 360, 361, 2664, 616, 3176, 104, 936, 680,
]

@[expose] public def m24ChunkMessage5 : Array (Fin 4096) := #[
  1192, 2216, 168, 169, 2856, 1320, 3369, 2344, 296, 1577, 1576, 552,
  2601, 1065, 41, 2088, 40, 3017, 1736, 1224, 201, 2248, 200, 840,
  3400, 1352, 2376, 329, 3656, 1609, 585, 584, 1096, 72, 2121, 73,
  1928, 904, 3464, 392, 393, 649, 2696, 3209, 3208, 1160, 136, 2185,
  137, 1800, 777, 1288, 1289, 2313, 265, 2312, 264, 3592, 1544, 2568,
  520, 2569, 521, 3080, 1032, 1033, 2057, 2056, 8, 1008, 240, 2289,
  1393, 368, 1648, 2672, 2160, 112, 2480, 688, 1200, 1201, 2224, 176,
  816, 3376, 2352, 304, 305, 1585, 561, 2608, 560, 3121, 1072, 48,
]

@[expose] public def m24ChunkMessage6 : Array (Fin 4096) := #[
  49, 465, 720, 3280, 1232, 208, 209, 3920, 1360, 2385, 2384, 336,
  1616, 592, 2641, 593, 1104, 1105, 81, 2128, 1936, 2960, 913, 1424,
  400, 1680, 2705, 3216, 1169, 2193, 145, 2192, 144, 785, 784, 1297,
  3344, 1296, 272, 2321, 273, 3600, 1552, 3601, 529, 2576, 528, 3088,
  1040, 2064, 16, 2065, 17, 3552, 480, 1760, 737, 225, 224, 865,
  2912, 1376, 2401, 1632, 608, 1121, 3168, 1120, 2144, 96, 2145, 97,
  1953, 1440, 416, 2465, 417, 1696, 2721, 2720, 672, 3232, 1184, 2208,
  161, 3872, 1824, 800, 801, 1312, 289, 2336, 288, 3616, 544, 2593,
]

@[expose] public def m24ChunkMessage7 : Array (Fin 4096) := #[
  545, 3104, 1056, 3105, 1057, 2081, 33, 2080, 32, 960, 1473, 449,
  2496, 448, 3776, 2752, 704, 705, 1216, 3265, 2240, 192, 1856, 1857,
  2880, 832, 1344, 2368, 320, 321, 1601, 2625, 2624, 576, 3137, 1089,
  3136, 1088, 2112, 64, 2113, 65, 2944, 896, 1409, 3456, 1408, 2432,
  384, 2433, 1664, 3713, 1665, 641, 2688, 640, 1153, 1152, 2176, 128,
  2177, 129, 3841, 1792, 2816, 768, 2817, 769, 3328, 3329, 1281, 257,
  2304, 256, 1537, 3584, 1536, 2560, 512, 513, 3072, 1024, 3073, 1025,
  2049, 1, 2048,
]

@[reducible, expose]
public def m24BlockMessageValue (i : Fin 759) : Fin 4096 :=
  if h0 : i.val < 96 then
    m24ChunkMessage0[i.val]'(by change i.val < 96; omega)
  else
  if h1 : i.val < 192 then
    m24ChunkMessage1[i.val - 96]'(by change i.val - 96 < 96; omega)
  else
  if h2 : i.val < 288 then
    m24ChunkMessage2[i.val - 192]'(by change i.val - 192 < 96; omega)
  else
  if h3 : i.val < 384 then
    m24ChunkMessage3[i.val - 288]'(by change i.val - 288 < 96; omega)
  else
  if h4 : i.val < 480 then
    m24ChunkMessage4[i.val - 384]'(by change i.val - 384 < 96; omega)
  else
  if h5 : i.val < 576 then
    m24ChunkMessage5[i.val - 480]'(by change i.val - 480 < 96; omega)
  else
  if h6 : i.val < 672 then
    m24ChunkMessage6[i.val - 576]'(by change i.val - 576 < 96; omega)
  else
    m24ChunkMessage7[i.val - 672]'(by change i.val - 672 < 87; omega)

/-- The reflected message of the octad with the given certificate index. -/
@[expose] public def m24BlockMessage (i : Fin 759) : Fin 4096 :=
  m24BlockMessageValue i

@[expose] public def m24BlockMessageInverseChunk0 : Array (Fin 759) := #[
  0, 757, 252, 250, 426, 428, 75, 76, 548, 0, 132, 130,
  306, 308, 0, 20, 626, 628, 170, 172, 348, 0, 36, 0,
  467, 468, 0, 92, 268, 267, 4, 0, 680, 678, 200, 0,
  375, 0, 46, 48, 496, 494, 104, 102, 279, 280, 0, 0,
  575, 576, 143, 0, 320, 318, 24, 0, 0, 440, 80, 0,
  0, 0, 0, 0, 711, 713, 218, 219, 395, 393, 57, 55,
  513, 515, 112, 0, 289, 0, 0, 0, 0, 594, 153, 0,
  328, 329, 0, 0, 449, 447, 83, 0, 0, 0, 1, 0,
  645, 647, 0, 181, 357, 0, 0, 0, 477, 0, 0, 95,
  271, 0, 5, 0, 557, 0, 135, 134, 0, 311, 0, 0,
  431, 0, 0, 0, 0, 0, 0, 0, 731, 733, 229, 231,
  408, 406, 0, 0, 526, 528, 120, 0, 295, 0, 13, 12,
  608, 606, 160, 158, 335, 0, 0, 29, 455, 0, 0, 0,
  261, 0, 0, 0, 0, 660, 187, 188, 363, 361, 41, 0,
  482, 483, 0, 0, 0, 0, 6, 0, 563, 0, 0, 0,
  0, 314, 0, 0, 434, 0, 78, 0, 0, 0, 0, 0,
  693, 0, 207, 0, 0, 382, 50, 0, 502, 500, 106, 0,
  0, 283, 0, 0, 581, 582, 0, 0, 323, 0, 25, 0,
  0, 0, 0, 81, 0, 0, 0, 0, 634, 633, 174, 0,
  351, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  253, 0, 0, 0, 745, 743, 240, 238, 414, 416, 67, 68,
  536, 534, 124, 0, 300, 0, 0, 0, 614, 616, 0, 0,
  340, 0, 0, 30, 458, 0, 87, 88, 264, 0, 0, 0,
  668, 666, 192, 0, 0, 368, 0, 0, 488, 0, 99, 0,
  0, 275, 7, 0, 567, 568, 0, 139, 0, 0, 23, 0,
  0, 0, 0, 0, 254, 0, 0, 0, 700, 701, 209, 211,
  387, 386, 52, 0, 0, 507, 0, 0, 0, 0, 10, 0,
  587, 0, 148, 0, 0, 0, 0, 0, 445, 0, 0, 0,
  0, 257, 0, 0, 0, 0, 177, 0, 353, 0, 0, 0,
  472, 473, 0, 0, 0, 0, 0, 0, 553, 0, 0, 0,
  309, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  720, 0, 0, 223, 399, 0, 60, 0, 519, 520, 0, 115,
  291, 0, 0, 0, 600, 0, 155, 0, 330, 331, 0, 0,
  451, 0, 0, 0, 0, 0, 0, 0, 650, 652, 183, 0,
  359, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 136, 0, 0, 0, 0, 0, 0, 432, 0, 0,
  0, 0, 0, 0, 685, 683, 0, 0, 0, 0, 0, 0,
  0, 0, 105, 0, 281, 0, 0, 0, 0, 577, 145, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  630, 0, 0, 0, 0, 0, 0, 37, 469, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk1 : Array (Fin 759) := #[
  750, 751, 0, 246, 422, 420, 70, 0, 540, 542, 125, 126,
  302, 0, 17, 0, 622, 620, 166, 0, 0, 342, 33, 34,
  462, 0, 90, 0, 0, 266, 0, 0, 670, 672, 195, 196,
  372, 0, 0, 44, 491, 0, 0, 0, 276, 0, 0, 0,
  572, 570, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0,
  255, 0, 0, 0, 705, 0, 215, 213, 390, 0, 0, 0,
  511, 510, 0, 0, 285, 0, 0, 11, 589, 591, 149, 0,
  325, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  640, 0, 179, 0, 354, 355, 0, 0, 475, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0,
  0, 429, 0, 0, 0, 0, 0, 0, 727, 725, 225, 0,
  401, 402, 61, 0, 0, 521, 118, 0, 0, 0, 0, 0,
  0, 0, 157, 0, 333, 0, 0, 0, 452, 453, 0, 0,
  0, 0, 0, 0, 656, 0, 184, 0, 0, 0, 0, 0,
  479, 0, 0, 0, 0, 273, 0, 0, 559, 0, 0, 137,
  313, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  688, 689, 0, 203, 0, 0, 49, 0, 0, 0, 0, 0,
  282, 0, 0, 0, 578, 0, 0, 0, 0, 0, 0, 0,
  442, 0, 0, 0, 0, 0, 0, 0, 0, 632, 0, 0,
  0, 0, 0, 0, 0, 0, 93, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 737, 739, 233, 0, 0, 0, 66, 0,
  0, 530, 122, 0, 298, 296, 0, 0, 610, 609, 162, 0,
  337, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  663, 664, 0, 0, 364, 0, 42, 0, 0, 0, 0, 98,
  0, 0, 0, 0, 564, 0, 0, 0, 0, 0, 0, 0,
  435, 0, 0, 0, 0, 0, 0, 0, 697, 0, 0, 0,
  0, 383, 0, 0, 503, 0, 107, 0, 0, 0, 0, 0,
  0, 0, 0, 147, 324, 0, 0, 0, 444, 0, 0, 0,
  0, 0, 0, 0, 0, 635, 175, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  715, 0, 221, 220, 0, 397, 0, 0, 517, 0, 0, 0,
  0, 0, 0, 0, 0, 598, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
  358, 0, 0, 0, 478, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 681, 0, 0, 0, 377, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 549, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk2 : Array (Fin 759) := #[
  753, 755, 247, 0, 425, 423, 73, 0, 544, 545, 127, 129,
  0, 303, 18, 0, 624, 0, 168, 167, 343, 345, 35, 0,
  465, 463, 0, 0, 0, 0, 0, 0, 674, 676, 197, 198,
  373, 0, 45, 0, 0, 493, 0, 0, 278, 0, 0, 0,
  574, 0, 142, 0, 317, 0, 0, 0, 437, 0, 0, 0,
  0, 0, 0, 0, 709, 707, 217, 0, 0, 0, 0, 54,
  512, 0, 110, 0, 286, 287, 0, 0, 592, 593, 0, 151,
  326, 0, 0, 0, 0, 0, 0, 0, 259, 0, 0, 0,
  643, 641, 0, 0, 0, 356, 38, 0, 0, 0, 94, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  430, 0, 0, 0, 0, 0, 0, 0, 729, 728, 227, 0,
  404, 405, 0, 63, 525, 0, 119, 0, 0, 0, 0, 0,
  0, 604, 0, 0, 0, 0, 28, 0, 0, 454, 84, 0,
  260, 0, 0, 0, 658, 0, 0, 185, 0, 0, 0, 0,
  480, 0, 0, 0, 274, 0, 0, 0, 560, 561, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  690, 0, 204, 205, 379, 0, 0, 0, 499, 0, 0, 0,
  0, 0, 0, 0, 580, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  350, 0, 0, 0, 0, 470, 0, 0, 0, 0, 0, 0,
  0, 0, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 742, 236, 237, 412, 0, 0, 0,
  531, 532, 0, 0, 299, 0, 14, 0, 613, 611, 163, 0,
  0, 338, 0, 0, 0, 0, 86, 0, 0, 0, 0, 0,
  665, 0, 0, 189, 366, 365, 0, 0, 485, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  436, 0, 0, 0, 0, 0, 0, 0, 698, 0, 0, 0,
  384, 0, 0, 0, 505, 0, 0, 108, 0, 0, 0, 0,
  584, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 637, 0, 176, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 552, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  718, 716, 222, 0, 0, 0, 58, 0, 0, 0, 0, 0,
  0, 290, 0, 0, 599, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 649, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 312, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 682, 0, 0, 378, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 441, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk3 : Array (Fin 759) := #[
  748, 746, 243, 241, 417, 418, 0, 0, 538, 0, 0, 0,
  0, 0, 16, 0, 618, 0, 0, 165, 0, 0, 0, 0,
  460, 0, 0, 0, 265, 0, 0, 0, 0, 0, 193, 0,
  0, 370, 0, 0, 490, 489, 100, 0, 0, 0, 0, 0,
  0, 569, 0, 0, 316, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 702, 212, 0, 389, 0, 53, 0,
  0, 509, 0, 0, 0, 0, 0, 0, 588, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 82, 0, 0, 0, 0, 0,
  639, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 554, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 722, 724, 0, 0,
  400, 0, 0, 0, 0, 0, 0, 116, 292, 0, 0, 0,
  601, 0, 156, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 653, 0, 0, 0, 0, 0, 40, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 498, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 322, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 631, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 735, 0, 232, 0, 409, 0, 0, 65,
  529, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  336, 0, 0, 0, 0, 456, 0, 0, 0, 0, 0, 0,
  662, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 138, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 694, 695, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 269, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 516, 0, 0, 0,
  0, 0, 0, 0, 596, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 648, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 201, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk4 : Array (Fin 759) := #[
  758, 756, 251, 249, 0, 427, 74, 0, 547, 546, 131, 0,
  305, 307, 19, 0, 625, 627, 169, 171, 347, 346, 0, 0,
  466, 0, 0, 0, 0, 0, 3, 0, 679, 677, 199, 0,
  374, 376, 0, 47, 495, 0, 103, 0, 0, 0, 0, 0,
  0, 0, 0, 144, 319, 0, 0, 0, 438, 439, 0, 0,
  256, 0, 0, 0, 710, 712, 0, 0, 394, 0, 56, 0,
  0, 514, 111, 113, 288, 0, 0, 0, 595, 0, 152, 0,
  327, 0, 0, 27, 448, 0, 0, 0, 0, 0, 0, 0,
  644, 646, 180, 0, 0, 0, 39, 0, 0, 0, 0, 0,
  0, 270, 0, 0, 556, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 730, 732, 228, 230,
  407, 0, 64, 0, 0, 527, 0, 0, 294, 0, 0, 0,
  607, 605, 159, 0, 0, 0, 0, 0, 0, 0, 85, 0,
  0, 262, 0, 0, 659, 0, 0, 0, 362, 0, 0, 0,
  481, 0, 0, 97, 0, 0, 0, 0, 562, 0, 0, 0,
  0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  692, 0, 0, 206, 380, 381, 0, 0, 501, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 173, 0,
  0, 0, 0, 0, 471, 0, 0, 0, 0, 0, 0, 0,
  0, 551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 744, 0, 239, 0, 413, 415, 0, 0,
  535, 533, 123, 0, 0, 0, 0, 15, 0, 615, 164, 0,
  339, 0, 31, 0, 0, 459, 0, 0, 0, 0, 0, 0,
  667, 0, 191, 190, 367, 0, 0, 0, 487, 0, 0, 0,
  0, 0, 0, 0, 566, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 699, 0, 0, 210,
  0, 0, 0, 0, 506, 0, 0, 0, 284, 0, 0, 0,
  586, 585, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 638, 0, 0, 352, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0,
  719, 721, 0, 0, 0, 398, 59, 0, 0, 0, 114, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  450, 0, 0, 0, 0, 0, 0, 0, 0, 651, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 272, 0, 0, 0,
  558, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 684, 0, 202, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  321, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk5 : Array (Fin 759) := #[
  749, 0, 244, 245, 421, 419, 69, 0, 539, 541, 0, 0,
  0, 0, 0, 0, 621, 0, 0, 0, 341, 0, 0, 0,
  461, 0, 0, 89, 0, 0, 0, 0, 0, 671, 194, 0,
  371, 0, 0, 0, 0, 492, 0, 0, 0, 0, 8, 0,
  571, 0, 140, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 704, 703, 214, 0, 0, 391, 0, 0,
  0, 0, 109, 0, 0, 0, 0, 0, 0, 590, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 258, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 474, 0, 0, 0,
  0, 0, 0, 0, 555, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 726, 0, 0, 0,
  0, 0, 0, 62, 522, 0, 117, 0, 293, 0, 0, 0,
  0, 602, 0, 0, 332, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 655, 654, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  687, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  349, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 736, 738, 0, 234, 410, 0, 0, 0,
  0, 0, 0, 0, 297, 0, 0, 0, 0, 0, 161, 0,
  0, 0, 0, 0, 457, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 484, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 315, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 696, 0, 0, 0,
  0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 636, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  714, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 597, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 497, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk6 : Array (Fin 759) := #[
  752, 754, 0, 248, 424, 0, 72, 71, 543, 0, 0, 128,
  304, 0, 0, 0, 623, 0, 0, 0, 0, 344, 0, 0,
  464, 0, 91, 0, 0, 0, 0, 0, 673, 675, 0, 0,
  0, 0, 0, 0, 0, 0, 101, 0, 277, 0, 0, 0,
  0, 573, 141, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 708, 706, 216, 0, 392, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 0,
  0, 0, 0, 0, 0, 446, 0, 0, 0, 0, 0, 0,
  642, 0, 0, 0, 0, 0, 0, 0, 476, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 310, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 226, 0,
  403, 0, 0, 0, 524, 523, 0, 0, 0, 0, 0, 0,
  603, 0, 0, 0, 334, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 657, 0, 186, 0, 0, 360, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 691, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 9, 0, 579, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 740, 741, 235, 0, 411, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 612, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 263, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 43, 0, 0, 486, 0, 0,
  0, 0, 0, 0, 565, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 0,
  0, 385, 0, 0, 504, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  717, 0, 0, 0, 0, 0, 0, 0, 518, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 154, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  629, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[expose] public def m24BlockMessageInverseChunk7 : Array (Fin 759) := #[
  747, 0, 242, 0, 0, 0, 0, 0, 537, 0, 0, 0,
  0, 301, 0, 0, 617, 619, 0, 0, 0, 0, 32, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 669, 0, 0, 0,
  369, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 388, 0, 0, 0,
  508, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 178, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 723, 224, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 433, 0, 0, 0, 0, 0, 0, 0,
  686, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 734, 0, 0, 0, 0, 0, 0,
  0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  661, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  583, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 396, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
]

@[reducible]
private def m24BlockMessageInverseValue (u : Fin 4096) : Fin 759 :=
  if h0 : u.val < 512 then
    m24BlockMessageInverseChunk0[u.val - 0]'(by change u.val - 0 < 512; omega)
  else
  if h1 : u.val < 1024 then
    m24BlockMessageInverseChunk1[u.val - 512]'(by change u.val - 512 < 512; omega)
  else
  if h2 : u.val < 1536 then
    m24BlockMessageInverseChunk2[u.val - 1024]'(by change u.val - 1024 < 512; omega)
  else
  if h3 : u.val < 2048 then
    m24BlockMessageInverseChunk3[u.val - 1536]'(by change u.val - 1536 < 512; omega)
  else
  if h4 : u.val < 2560 then
    m24BlockMessageInverseChunk4[u.val - 2048]'(by change u.val - 2048 < 512; omega)
  else
  if h5 : u.val < 3072 then
    m24BlockMessageInverseChunk5[u.val - 2560]'(by change u.val - 2560 < 512; omega)
  else
  if h6 : u.val < 3584 then
    m24BlockMessageInverseChunk6[u.val - 3072]'(by change u.val - 3072 < 512; omega)
  else
    m24BlockMessageInverseChunk7[u.val - 3584]'(by change u.val - 3584 < 512; omega)

private theorem m24BlockMessageDecode_spec :
    ∀ i : Fin 759, m24BlockMessageInverseValue (m24BlockMessage i) = i := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The incidence mask of the octad with the given certificate index. -/
@[expose] public def m24ChunkMask0 : Array Nat := #[
  133183, 8654942, 1950, 122910, 7864350, 2131054, 852142, 4215086, 9445934, 4204750, 1245518, 541263,
  1085583, 10633358, 8947982, 2367759, 2169358, 4620814, 1330190, 668686, 12649487, 4260470, 2109622, 1343798,
  8930358, 688342, 2115926, 1057879, 9504918, 4472983, 594199, 12722454, 797206, 1200662, 10519063, 4234262,
  2556950, 8389095, 1579110, 417894, 51878, 5375142, 2753318, 77094, 267815, 14944294, 8622118, 4759591,
  3227687, 3408582, 87238, 45894, 4982086, 8523334, 362567, 6426695, 11083846, 13680710, 399750, 1597830,
  6390150, 13111942, 205447, 2624647, 8692870, 5245703, 8733446, 11539718, 181511, 6317574, 1672710, 8419335,
  3319814, 4933638, 5582854, 2936838, 10354695, 532858, 12615866, 2376250, 1119290, 2162907, 1083994, 4342874,
  546970, 1450138, 4524314, 2265370, 9453851, 4207131, 9110042, 10497050, 820251, 135914, 8472682, 5505131,
]

@[expose] public def m24ChunkMask1 : Array Nat := #[
  3148202, 25771, 99115, 8783146, 4722218, 309290, 11014187, 6496298, 1753130, 311754, 9962698, 14680906,
  7499, 337482, 3016778, 3174474, 4821066, 8560715, 8466826, 4850059, 8653451, 2663050, 5325450, 232586,
  6558858, 158474, 1839882, 5285130, 2704650, 8443402, 3278347, 13768714, 1648651, 6342667, 479243, 13393930,
  11894794, 265458, 53363, 11665522, 213426, 1573555, 8395570, 6292787, 173618, 5269554, 2721842, 5115954,
  8724531, 5247442, 8413906, 394067, 8488274, 2627154, 211026, 13109331, 6594642, 1917010, 43411, 11272594,
  6425234, 365202, 8524947, 4793490, 3196050, 3220242, 4768530, 1707282, 292114, 85523, 13895186, 3414035,
  8833042, 10006546, 14766098, 2777107, 5472275, 1155298, 6832354, 1066850, 4360546, 2429282, 2108003, 9208418,
  12596322, 722019, 4465570, 562594, 10552994, 4266147, 9054370, 9719970, 2523299, 805155, 1192227, 10543394,
]

@[expose] public def m24ChunkMask2 : Array Nat := #[
  14221602, 1509922, 619042, 7377442, 12730915, 2251810, 9473059, 3941410, 4572194, 592834, 2237890, 4228803,
  10524866, 1198275, 798915, 13041858, 9709890, 9064770, 4284739, 3703107, 4479554, 9507395, 5907010, 2343490,
  584770, 7408706, 1479746, 10765379, 2118531, 9601922, 12602754, 1377667, 1064578, 935554, 2451586, 6064258,
  4386946, 3870850, 15736963, 9027715, 2395906, 4396802, 8922883, 6830338, 1169666, 10684675, 12882179, 1024258,
  7749890, 694787, 12691970, 12077570, 10891778, 1368579, 7143939, 9247746, 4598787, 2208771, 5788675, 9659394,
  15369218, 1065212, 10551612, 561724, 4465724, 4227421, 2237020, 592988, 2394268, 4395164, 8921245, 1063196,
  934172, 12601884, 1376797, 2118685, 9602076, 265068, 77933, 13238380, 172460, 6292141, 8395948, 1574189,
  214572, 2648108, 5343276, 3543084, 8699949, 2625996, 8487628, 394445, 8414540, 5248588, 186444, 11536461,
]

@[expose] public def m24ChunkMask3 : Array Nat := #[
  1876044, 6635596, 84365, 13894028, 1706636, 291468, 3220620, 4768908, 8524557, 4793100, 3195660, 6425868,
  365836, 44557, 11273740, 4986893, 8857612, 14725132, 10047500, 5398541, 2850829, 136564, 8431732, 2883701,
  4721076, 8782516, 99509, 25397, 3149364, 350260, 13635637, 1777716, 6471732, 336340, 6869, 14681300,
  9962324, 312916, 5638228, 4747348, 3248212, 8601685, 8442260, 3277205, 5284500, 2704020, 158868, 1840276,
  232212, 6558484, 8654101, 2663700, 5326100, 8467988, 4851221, 11147284, 6367253, 1624085, 438293, 11821076,
  13467668, 534244, 2296036, 4493540, 7348580, 639332, 10506852, 1213029, 4213861, 9765988, 1119140, 2377124,
  1321125, 676005, 12673188, 12091556, 12617508, 2136357, 9586980, 9187620, 4653349, 4340260, 8981029, 2466340,
  6046244, 953380, 1111076, 6886436, 10626085, 4342724, 1084868, 9193668, 9580740, 2154693, 5832901, 2164549,
]

@[expose] public def m24ChunkMask4 : Array Nat := #[
  12654916, 665925, 1331525, 10912068, 1141316, 6851140, 987716, 12853829, 2374724, 8950853, 4432964, 3818564,
  10496900, 820101, 4208005, 9110916, 4525700, 2266756, 9455237, 637060, 7362692, 12748933, 10817669, 7217284,
  1556612, 548612, 1451780, 4516100, 4000004, 2322692, 5935364, 9543941, 15220997, 9738756, 2509317, 3682821,
  4313605, 9101828, 15925764, 1252357, 14167044, 10603524, 12997636, 877573, 7635973, 8390265, 6297720, 491640,
  266681, 76472, 2753720, 5374776, 52536, 10225720, 8548408, 3186745, 4800569, 8522200, 4981464, 46296,
  86872, 3409240, 288857, 1708121, 13705304, 11059288, 6316440, 1671576, 11539096, 180889, 5246105, 8733848,
  2624281, 8692504, 13112600, 206105, 400920, 1599000, 6391320, 8493081, 4892696, 3360792, 2961432, 5558296,
  15073305, 4261352, 559337, 10756328, 9474408, 2244969, 4252264, 3736168, 1191016, 808040, 8930216, 1345192,
]

@[expose] public def m24ChunkMask5 : Array Nat := #[
  4606120, 5779624, 2216104, 9633961, 2111272, 727336, 12593449, 1401128, 7110952, 1071657, 10652200, 12915240,
  926249, 2427945, 4363305, 9020456, 15746088, 1057737, 2117320, 1382600, 12603593, 745672, 7504072, 689992,
  2206024, 5785928, 4600136, 9240905, 8927816, 4393545, 2396745, 9847368, 12880968, 10687560, 6825033, 1164361,
  4234120, 2556808, 798088, 1201544, 10519945, 595593, 12723848, 2242697, 9496712, 15272072, 9343112, 4563081,
  3948681, 9506568, 4474633, 10770696, 1476873, 585993, 7409929, 12198152, 12828936, 7612936, 903688, 1290760,
  6967816, 10576393, 14189065, 4291592, 3709960, 9063433, 9712649, 2548744, 6226952, 2130928, 8982768, 4333809,
  1116529, 12861808, 674416, 1323632, 2188400, 5801072, 9446832, 4216496, 1218736, 10504369, 843952, 7667888,
  853808, 2500912, 4305200, 3690800, 9077041, 4491825, 2298417, 15213104, 9552432, 539697, 12782640, 10785840,
]

@[expose] public def m24ChunkMask6 : Array Nat := #[
  1459249, 542161, 1246928, 3680464, 4311248, 2511056, 9732305, 4206416, 825680, 10498385, 1237328, 7012688,
  10816080, 12751440, 631377, 7357009, 9460816, 2264145, 4527185, 9315408, 1330064, 668560, 12649361, 2170256,
  4621712, 8949392, 2369169, 12859536, 985233, 1142929, 6852753, 10723472, 14303376, 1087249, 10635024, 4348177,
  9005328, 15763728, 9900304, 6037777, 2474257, 2161168, 5839376, 9579025, 9196049, 4678160, 4096528, 1420304,
  7097360, 7484432, 775184, 12641297, 12125201, 31200, 1966560, 13634272, 344801, 3151073, 8570080, 4723553,
  8594272, 11013472, 304481, 106080, 6686304, 8788065, 5056608, 3459168, 2797664, 5460064, 9986145, 14778465,
  135073, 8751520, 14815648, 2695585, 5292449, 2890400, 8434337, 3302048, 4948640, 6335648, 1658016, 472224,
  13370529, 1616672, 6376224, 447264, 11797281, 5512480, 8475937, 4875552, 3376416, 8678944, 10098208, 5318177,
]

@[expose] public def m24ChunkMask7 : Array Nat := #[
  2672161, 11614240, 13162528, 256033, 7997473, 6582305, 1937441, 14065696, 11485216, 8656832, 6556097, 233921,
  13148608, 11616704, 436928, 6369984, 1626816, 11141825, 4857024, 8465601, 5530816, 2983104, 3283776, 8440641,
  2908992, 5604160, 478528, 1652032, 6346048, 13763905, 1838657, 161345, 11576896, 13190720, 5290049, 2709569,
  14837824, 10192960, 8777792, 16519232, 3612737, 5161025, 124800, 7866240, 9968001, 5450112, 2804096, 3453312,
  5067136, 8806785, 8608384, 4745857, 3246721, 5640833, 10297984, 14992000, 318593, 11930752, 11039872, 13735040,
  1746049, 6505601, 342785, 13503232, 13660928, 11113216, 6464257, 1786625, 8568064, 3173633, 4820225, 3020033,
  15017216, 10274048, 14687745, 2829824, 5426688, 5027328, 3495424, 8881665, 1996800, 6789120, 11315201, 13977601,
  13316097, 11718657, 7987200,
]

@[reducible, expose]
public def m24BlockMaskValue (i : Fin 759) : Nat :=
  if h0 : i.val < 96 then
    m24ChunkMask0[i.val]'(by change i.val < 96; omega)
  else
  if h1 : i.val < 192 then
    m24ChunkMask1[i.val - 96]'(by change i.val - 96 < 96; omega)
  else
  if h2 : i.val < 288 then
    m24ChunkMask2[i.val - 192]'(by change i.val - 192 < 96; omega)
  else
  if h3 : i.val < 384 then
    m24ChunkMask3[i.val - 288]'(by change i.val - 288 < 96; omega)
  else
  if h4 : i.val < 480 then
    m24ChunkMask4[i.val - 384]'(by change i.val - 384 < 96; omega)
  else
  if h5 : i.val < 576 then
    m24ChunkMask5[i.val - 480]'(by change i.val - 480 < 96; omega)
  else
  if h6 : i.val < 672 then
    m24ChunkMask6[i.val - 576]'(by change i.val - 576 < 96; omega)
  else
    m24ChunkMask7[i.val - 672]'(by change i.val - 672 < 87; omega)

@[expose] public noncomputable def m24BlockMaskAt (i : Fin 759) : BitVec 24 :=
  BitVec.ofNat 24 (m24BlockMaskValue i)

/-- The octad with the given certificate index. -/
@[expose] public noncomputable def m24BlockAt (i : Fin 759) : Finset (Fin 24) :=
  Finset.univ.filter fun x => (m24BlockMaskAt i).getLsb x = true

/-- The chunk mask tables agree with the systematic Golay encoder. -/
private theorem m24BlockMaskValue_eq_golayMask :
    ∀ i : Fin 759, m24BlockMaskValue i = m24GolayMask (m24BlockMessage i) := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Every octad is a weight-eight word of the certified Golay code. -/
public theorem m24BlockAt_eq_m24GolayWord (i : Fin 759) :
    m24BlockAt i = m24GolayWord (m24BlockMessage i) := by
  rw [m24BlockAt, m24BlockMaskAt, m24GolayWord, m24GolayCode_eq_ofNat_mask,
    m24BlockMaskValue_eq_golayMask]

/-- Every octad of the concrete W24 design has size eight. -/
public theorem m24BlockAt_card : ∀ i, (m24BlockAt i).card = 8 := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The reflected message table is injective. -/
public theorem m24BlockMessage_injective : Function.Injective m24BlockMessage := by
  have hdecode : ∀ i : Fin 759,
      m24BlockMessageInverseValue (m24BlockMessage i) = i :=
    m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro i j hij
  rw [← hdecode i, ← hdecode j, hij]

@[expose] public def m24PermuteMask (g : Equiv.Perm (Fin 24))
    (x : BitVec 24) : BitVec 24 :=
  BitVec.ofFnLE fun i => x.getLsb (g.symm i)

public theorem m24_smul_blockAt_of_mask_eq
    (g : Equiv.Perm (Fin 24)) (i j : Fin 759)
    (h : m24PermuteMask g (m24BlockMaskAt i) = m24BlockMaskAt j) :
    g • m24BlockAt i = m24BlockAt j := by
  ext x
  rw [← Finset.inv_smul_mem_iff]
  simp only [m24BlockAt, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.smul_def, Equiv.Perm.inv_def]
  rw [← h]
  simp [m24PermuteMask]

/-- The explicit finite set of all 759 octads. -/

@[expose] public noncomputable def m24Blocks : Finset (Finset (Fin 24)) :=
  Finset.univ.image m24BlockAt


public theorem m24BlocksCardinalityCheck : m24Blocks.card = 759 := by
  rw [m24Blocks, Finset.card_image_of_injective _ (by
    intro i j hij
    apply m24BlockMessage_injective
    apply m24GolayWord_injective
    simpa only [m24BlockAt_eq_m24GolayWord] using hij)]
  simp

public theorem m24BlockAt_inter (i j : Fin 759) (hij : i ≠ j) :
    (m24BlockAt i ∩ m24BlockAt j).card < 5 := by
  rw [m24BlockAt_eq_m24GolayWord i, m24BlockAt_eq_m24GolayWord j]
  apply m24Golay_inter_lt_five
  · rw [← m24BlockAt_eq_m24GolayWord i]
    exact m24BlockAt_card i
  · rw [← m24BlockAt_eq_m24GolayWord j]
    exact m24BlockAt_card j
  · apply m24Golay_minWeight
    apply m24GolayMessageXor_ne_zero
    intro hmsg
    exact hij (m24BlockMessage_injective hmsg)

@[expose] public def m24GeneratorABlockIndexChunk0 : Array (Fin 759) := #[
  85, 156, 25, 136, 158, 597, 334, 607, 551, 313, 453, 578,
  331, 261, 600, 560, 581, 441, 604, 434, 608, 146, 22, 154,
  159, 2, 157, 137, 29, 28, 160, 78, 133, 81, 145, 155,
  84, 332, 602, 433, 321, 262, 443, 562, 579, 603, 450, 558,
  605, 322, 333, 549, 601, 442, 596, 452, 559, 598, 260, 314,
  330, 323, 253, 335, 312, 582, 580, 606, 451, 550, 577, 563,
  432, 455, 561, 599, 454, 140, 31, 150, 171, 33, 147, 90,
  36, 0, 168, 87, 172, 135, 83, 143, 163, 258, 621, 619,
]

@[expose] public def m24GeneratorABlockIndexChunk1 : Array (Fin 759) := #[
  346, 319, 586, 464, 595, 565, 625, 438, 459, 336, 342, 589,
  622, 554, 460, 570, 610, 435, 320, 268, 326, 309, 329, 264,
  343, 431, 593, 568, 626, 587, 447, 468, 576, 614, 465, 574,
  611, 32, 161, 89, 3, 27, 152, 169, 77, 144, 164, 91,
  141, 34, 21, 82, 162, 149, 79, 166, 138, 165, 23, 35,
  1, 26, 4, 24, 30, 134, 148, 92, 142, 153, 151, 167,
  86, 139, 170, 80, 88, 315, 341, 590, 457, 617, 555, 583,
  571, 461, 310, 339, 327, 347, 256, 344, 263, 623, 439, 566,
]

@[expose] public def m24GeneratorABlockIndexChunk2 : Array (Fin 759) := #[
  627, 446, 556, 585, 448, 466, 615, 573, 612, 325, 255, 324,
  337, 266, 316, 265, 569, 462, 572, 609, 588, 591, 429, 444,
  564, 620, 456, 618, 328, 257, 348, 345, 311, 259, 317, 338,
  254, 267, 318, 340, 584, 449, 557, 575, 616, 467, 613, 436,
  463, 445, 553, 594, 430, 552, 592, 624, 437, 567, 628, 440,
  458, 62, 228, 202, 186, 221, 93, 225, 58, 13, 41, 188,
  119, 207, 205, 229, 115, 686, 655, 522, 272, 380, 407, 732,
  501, 659, 721, 523, 717, 401, 377, 292, 656, 689, 517, 725,
]

@[expose] public def m24GeneratorABlockIndexChunk3 : Array (Fin 759) := #[
  648, 722, 408, 405, 283, 350, 361, 399, 502, 634, 683, 526,
  718, 630, 690, 729, 480, 650, 733, 483, 519, 117, 182, 224,
  64, 9, 59, 173, 206, 226, 230, 97, 114, 40, 49, 61,
  203, 201, 116, 184, 220, 118, 60, 12, 37, 50, 6, 63,
  105, 204, 227, 183, 231, 174, 106, 120, 187, 223, 96, 185,
  222, 349, 293, 396, 654, 714, 687, 497, 726, 723, 381, 403,
  360, 294, 362, 398, 684, 719, 527, 657, 524, 471, 692, 629,
  691, 518, 651, 730, 481, 282, 397, 400, 273, 358, 402, 688,
]

@[expose] public def m24GeneratorABlockIndexChunk4 : Array (Fin 759) := #[
  727, 479, 724, 516, 632, 681, 498, 631, 653, 715, 478, 521,
  351, 378, 363, 295, 379, 281, 382, 359, 406, 291, 404, 274,
  290, 693, 470, 649, 728, 482, 520, 652, 731, 682, 499, 633,
  685, 469, 500, 528, 660, 720, 525, 658, 716, 214, 244, 121,
  72, 39, 19, 113, 239, 248, 103, 190, 251, 17, 53, 42,
  215, 241, 193, 126, 196, 233, 46, 68, 55, 10, 76, 73,
  218, 176, 252, 104, 110, 181, 209, 240, 99, 130, 197, 237,
  127, 421, 410, 369, 738, 539, 636, 703, 492, 747, 394, 385,
]

@[expose] public def m24GeneratorABlockIndexChunk5 : Array (Fin 759) := #[
  304, 376, 413, 307, 644, 547, 679, 675, 740, 712, 506, 708,
  476, 752, 535, 667, 756, 355, 390, 418, 422, 276, 296, 503,
  663, 751, 490, 748, 640, 511, 694, 509, 735, 540, 670, 739,
  387, 286, 373, 308, 414, 395, 271, 279, 368, 426, 299, 366,
  423, 713, 709, 753, 532, 668, 757, 494, 536, 641, 698, 473,
  513, 645, 701, 680, 743, 548, 676, 485, 545, 51, 69, 8,
  245, 242, 109, 178, 194, 234, 47, 56, 15, 74, 43, 71,
  216, 101, 191, 249, 123, 208, 111, 180, 210, 199, 131, 235,
]

@[expose] public def m24GeneratorABlockIndexChunk6 : Array (Fin 759) := #[
  128, 70, 11, 44, 66, 16, 65, 179, 232, 195, 98, 125,
  212, 107, 175, 213, 246, 122, 243, 100, 54, 5, 57, 75,
  14, 52, 38, 45, 18, 48, 67, 7, 20, 211, 112, 132,
  200, 238, 129, 198, 236, 177, 219, 95, 217, 94, 108, 189,
  247, 102, 124, 192, 250, 371, 301, 391, 388, 419, 297, 704,
  474, 749, 661, 696, 508, 537, 669, 734, 484, 541, 671, 736,
  288, 411, 305, 374, 415, 392, 352, 270, 284, 367, 427, 277,
  424, 638, 710, 504, 706, 754, 758, 495, 533, 642, 514, 646,
]

@[expose] public def m24GeneratorABlockIndexChunk7 : Array (Fin 759) := #[
  699, 677, 744, 487, 546, 673, 741, 486, 543, 389, 417, 298,
  364, 420, 269, 354, 383, 285, 302, 372, 370, 409, 510, 697,
  639, 695, 538, 672, 737, 542, 702, 475, 635, 705, 664, 750,
  491, 530, 662, 746, 489, 529, 353, 393, 428, 280, 300, 365,
  425, 278, 289, 357, 386, 287, 356, 384, 412, 303, 375, 416,
  275, 306, 643, 512, 647, 700, 472, 515, 488, 678, 745, 544,
  674, 742, 711, 477, 507, 637, 707, 505, 493, 531, 665, 755,
  496, 534, 666,
]

@[reducible, expose]
public def m24GeneratorABlockIndexValue (i : Fin 759) : Fin 759 :=
  if h0 : i.val < 96 then
    m24GeneratorABlockIndexChunk0[i.val]'(by change i.val < 96; omega)
  else
  if h1 : i.val < 192 then
    m24GeneratorABlockIndexChunk1[i.val - 96]'(by change i.val - 96 < 96; omega)
  else
  if h2 : i.val < 288 then
    m24GeneratorABlockIndexChunk2[i.val - 192]'(by change i.val - 192 < 96; omega)
  else
  if h3 : i.val < 384 then
    m24GeneratorABlockIndexChunk3[i.val - 288]'(by change i.val - 288 < 96; omega)
  else
  if h4 : i.val < 480 then
    m24GeneratorABlockIndexChunk4[i.val - 384]'(by change i.val - 384 < 96; omega)
  else
  if h5 : i.val < 576 then
    m24GeneratorABlockIndexChunk5[i.val - 480]'(by change i.val - 480 < 96; omega)
  else
  if h6 : i.val < 672 then
    m24GeneratorABlockIndexChunk6[i.val - 576]'(by change i.val - 576 < 96; omega)
  else
    m24GeneratorABlockIndexChunk7[i.val - 672]'(by change i.val - 672 < 87; omega)

@[expose] public def m24GeneratorABlockIndex (i : Fin 759) : Fin 759 :=
  m24GeneratorABlockIndexValue i

@[expose] public def m24GeneratorBBlockIndexChunk0 : Array (Fin 759) := #[
  588, 149, 549, 258, 591, 79, 602, 337, 622, 156, 161, 34,
  452, 333, 456, 610, 617, 462, 316, 570, 571, 152, 581, 445,
  311, 81, 26, 135, 579, 323, 585, 587, 593, 328, 449, 430,
  556, 155, 167, 36, 260, 563, 616, 565, 575, 624, 466, 468,
  347, 160, 22, 87, 139, 142, 91, 170, 171, 4, 599, 331,
  450, 606, 607, 561, 434, 613, 339, 567, 254, 320, 439, 343,
  465, 344, 625, 267, 628, 147, 442, 325, 555, 146, 82, 21,
  322, 578, 583, 444, 324, 589, 590, 554, 429, 157, 32, 166,
]

@[expose] public def m24GeneratorBBlockIndexChunk1 : Array (Fin 759) := #[
  596, 313, 457, 564, 569, 460, 620, 621, 266, 2, 137, 162,
  138, 140, 165, 33, 89, 90, 597, 598, 601, 453, 332, 433,
  559, 336, 609, 435, 315, 255, 572, 618, 619, 265, 341, 342,
  461, 133, 1, 153, 321, 582, 584, 553, 431, 326, 446, 594,
  595, 145, 25, 148, 77, 134, 150, 151, 83, 27, 441, 577,
  580, 443, 550, 551, 253, 586, 257, 552, 309, 310, 557, 592,
  259, 447, 327, 329, 448, 85, 29, 23, 86, 164, 168, 92,
  143, 144, 600, 432, 562, 603, 604, 335, 455, 338, 614, 264,
]

@[expose] public def m24GeneratorBBlockIndexChunk2 : Array (Fin 759) := #[
  615, 623, 346, 467, 348, 317, 437, 576, 256, 154, 136, 78,
  84, 28, 158, 159, 163, 30, 31, 88, 35, 169, 172, 3,
  0, 141, 80, 24, 330, 451, 312, 558, 560, 314, 334, 454,
  261, 605, 608, 262, 436, 566, 568, 611, 263, 612, 458, 459,
  340, 463, 464, 345, 626, 268, 627, 573, 574, 438, 318, 319,
  440, 49, 696, 510, 640, 107, 215, 178, 498, 687, 689, 694,
  383, 389, 704, 354, 475, 232, 244, 246, 517, 727, 653, 664,
  371, 418, 537, 750, 302, 220, 117, 184, 42, 195, 16, 243,
]

@[expose] public def m24GeneratorBBlockIndexChunk3 : Array (Fin 759) := #[
  126, 69, 396, 715, 724, 401, 655, 273, 737, 738, 298, 662,
  484, 490, 672, 746, 747, 540, 419, 422, 541, 177, 110, 219,
  682, 693, 471, 387, 643, 392, 711, 712, 289, 202, 204, 174,
  211, 5, 217, 55, 111, 56, 281, 685, 502, 381, 350, 633,
  504, 700, 637, 473, 352, 644, 647, 707, 708, 287, 513, 395,
  514, 188, 226, 120, 240, 15, 75, 132, 45, 199, 719, 359,
  729, 406, 407, 528, 488, 531, 412, 743, 744, 753, 754, 547,
  428, 493, 279, 677, 680, 60, 96, 63, 229, 13, 230, 191,
]

@[expose] public def m24GeneratorBBlockIndexChunk4 : Array (Fin 759) := #[
  235, 237, 67, 124, 72, 129, 249, 252, 197, 102, 103, 48,
  718, 520, 650, 651, 657, 482, 363, 523, 404, 525, 730, 733,
  294, 365, 668, 299, 741, 413, 534, 535, 416, 544, 425, 757,
  305, 308, 758, 673, 676, 277, 375, 376, 496, 179, 212, 109,
  681, 686, 632, 697, 269, 702, 390, 511, 391, 201, 203, 93,
  51, 175, 53, 213, 214, 11, 377, 497, 688, 282, 631, 349,
  695, 503, 635, 636, 639, 355, 474, 508, 509, 388, 703, 285,
  705, 182, 116, 225, 122, 66, 17, 245, 193, 44, 397, 479,
]

@[expose] public def m24GeneratorBBlockIndexChunk5 : Array (Fin 759) := #[
  400, 725, 293, 726, 663, 734, 735, 410, 530, 417, 538, 749,
  751, 669, 491, 492, 372, 221, 40, 224, 61, 62, 118, 98,
  121, 65, 233, 234, 241, 242, 125, 70, 100, 194, 196, 8,
  516, 714, 648, 358, 478, 654, 656, 722, 292, 723, 521, 522,
  402, 661, 364, 409, 529, 296, 736, 739, 297, 748, 301, 539,
  420, 421, 542, 369, 489, 370, 670, 276, 671, 105, 206, 207,
  208, 52, 54, 218, 39, 95, 630, 351, 499, 379, 283, 692,
  638, 698, 506, 386, 507, 512, 710, 713, 288, 641, 642, 477,
]

@[expose] public def m24GeneratorBBlockIndexChunk6 : Array (Fin 759) := #[
  357, 37, 173, 205, 9, 50, 106, 176, 108, 209, 10, 210,
  216, 112, 113, 57, 38, 94, 180, 181, 378, 683, 684, 629,
  469, 470, 634, 690, 691, 380, 500, 501, 382, 472, 353, 384,
  385, 505, 699, 701, 284, 286, 706, 709, 393, 394, 515, 476,
  356, 645, 270, 271, 646, 58, 223, 227, 64, 187, 6, 238,
  239, 189, 99, 101, 200, 247, 248, 18, 130, 74, 76, 131,
  649, 518, 720, 721, 291, 728, 526, 408, 527, 480, 360, 659,
  660, 532, 411, 300, 745, 665, 367, 368, 487, 373, 678, 679,
]

@[expose] public def m24GeneratorBBlockIndexChunk7 : Array (Fin 759) := #[
  280, 752, 303, 304, 755, 426, 546, 548, 427, 183, 222, 114,
  115, 59, 119, 228, 12, 231, 185, 186, 41, 97, 236, 14,
  68, 123, 43, 190, 7, 192, 198, 46, 104, 47, 127, 71,
  73, 128, 19, 250, 251, 20, 272, 652, 716, 717, 290, 519,
  398, 399, 403, 405, 524, 731, 732, 295, 274, 658, 361, 481,
  483, 362, 740, 742, 414, 533, 536, 415, 485, 366, 486, 666,
  667, 275, 674, 675, 278, 494, 374, 495, 423, 543, 545, 424,
  756, 306, 307,
]

@[reducible, expose]
public def m24GeneratorBBlockIndexValue (i : Fin 759) : Fin 759 :=
  if h0 : i.val < 96 then
    m24GeneratorBBlockIndexChunk0[i.val]'(by change i.val < 96; omega)
  else
  if h1 : i.val < 192 then
    m24GeneratorBBlockIndexChunk1[i.val - 96]'(by change i.val - 96 < 96; omega)
  else
  if h2 : i.val < 288 then
    m24GeneratorBBlockIndexChunk2[i.val - 192]'(by change i.val - 192 < 96; omega)
  else
  if h3 : i.val < 384 then
    m24GeneratorBBlockIndexChunk3[i.val - 288]'(by change i.val - 288 < 96; omega)
  else
  if h4 : i.val < 480 then
    m24GeneratorBBlockIndexChunk4[i.val - 384]'(by change i.val - 384 < 96; omega)
  else
  if h5 : i.val < 576 then
    m24GeneratorBBlockIndexChunk5[i.val - 480]'(by change i.val - 480 < 96; omega)
  else
  if h6 : i.val < 672 then
    m24GeneratorBBlockIndexChunk6[i.val - 576]'(by change i.val - 576 < 96; omega)
  else
    m24GeneratorBBlockIndexChunk7[i.val - 672]'(by change i.val - 672 < 87; omega)

@[expose] public def m24GeneratorBBlockIndex (i : Fin 759) : Fin 759 :=
  m24GeneratorBBlockIndexValue i

public theorem m24Blocks_smul_of_reindex
    (g : Equiv.Perm (Fin 24)) (f : Fin 759 → Fin 759)
    (hf : Function.Surjective f)
    (hblock : ∀ i, g • m24BlockAt i = m24BlockAt (f i)) :
    g • m24Blocks = m24Blocks := by
  ext B
  constructor
  · intro hB
    rw [Finset.mem_smul_finset] at hB
    rcases hB with ⟨C, hC, rfl⟩
    rw [m24Blocks] at hC ⊢
    rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
    exact Finset.mem_image.mpr
      ⟨f i, Finset.mem_univ _, (hblock i).symm⟩
  · intro hB
    rw [m24Blocks] at hB
    rcases Finset.mem_image.mp hB with ⟨j, _, rfl⟩
    rcases hf j with ⟨i, rfl⟩
    rw [Finset.mem_smul_finset]
    refine ⟨m24BlockAt i, ?_, hblock i⟩
    rw [m24Blocks]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem m24GeneratorABlockIndex_involutive :
    ∀ j : Fin 759, m24GeneratorABlockIndex (m24GeneratorABlockIndex j) = j := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem m24GeneratorBBlockIndex_cube :
    ∀ j : Fin 759,
      m24GeneratorBBlockIndex (m24GeneratorBBlockIndex (m24GeneratorBBlockIndex j)) = j := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem m24GeneratorA_mask_action :
    ∀ j : Fin 759,
      m24PermuteMask m24GeneratorA (m24BlockMaskAt j) =
        m24BlockMaskAt (m24GeneratorABlockIndex j) := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem m24GeneratorB_mask_action :
    ∀ j : Fin 759,
      m24PermuteMask m24GeneratorB (m24BlockMaskAt j) =
        m24BlockMaskAt (m24GeneratorBBlockIndex j) := by
  exact m24ForallFin759_of_chunks
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The first standard generator preserves the concrete W24 block set. -/
public theorem m24GeneratorA_blocks_smul : m24GeneratorA • m24Blocks = m24Blocks := by
  apply m24Blocks_smul_of_reindex m24GeneratorA m24GeneratorABlockIndex
  · intro i
    exact ⟨m24GeneratorABlockIndex i, m24GeneratorABlockIndex_involutive i⟩
  · intro i
    exact m24_smul_blockAt_of_mask_eq m24GeneratorA i
      (m24GeneratorABlockIndex i) (m24GeneratorA_mask_action i)

/-- The second standard generator preserves the concrete W24 block set. -/
public theorem m24GeneratorB_blocks_smul : m24GeneratorB • m24Blocks = m24Blocks := by
  apply m24Blocks_smul_of_reindex m24GeneratorB m24GeneratorBBlockIndex
  · intro i
    exact ⟨m24GeneratorBBlockIndex (m24GeneratorBBlockIndex i),
      m24GeneratorBBlockIndex_cube i⟩
  · intro i
    apply m24_smul_blockAt_of_mask_eq m24GeneratorB i
      (m24GeneratorBBlockIndex i)
    exact m24GeneratorB_mask_action i

end Sporadic.Mathieu
