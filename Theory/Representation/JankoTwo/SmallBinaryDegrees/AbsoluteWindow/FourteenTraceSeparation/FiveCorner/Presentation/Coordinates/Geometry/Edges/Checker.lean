module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Edges.Tables
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.SchreierData

/-!
# Soundness of the cached J₂ edge checker

Blockwise equality and elementary digit arithmetic identify the flattened
integers with the original packed lookups. The transversal cache is compared
to each of the four certified normal-form factors; the power cache is checked
against the literal left and right subgroup generators. Thus every Boolean
edge check implies exactly the four-point permutation equation in `EdgeChecks`.
The small cache comparisons are kernel checked here; all 24192 rows are checked
in `Edges.Checks` and assembled in `Geometry.Edges`.

Source: Geometry/source/README.md and the unchanged data and ATLAS attribution
in Coordinates/source/README.md and Presentation/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Edges
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
theorem digit_mod (c a b w : Nat) (h : a+w ≤ b) :
    ((c % 2^b) >>> a) % 2^w = (c >>> a) % 2^w := by
  simp only [Nat.shiftRight_eq_div_pow]
  have hb : b = a + (b-a) := by omega
  conv_lhs => rw [hb, Nat.pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

theorem flatLookup_eq (w code : Nat) (a : Array Nat)
    (h : ∀ i : Fin 189, a[i.val]! = (code >>> (w*128*i.val)) % 2^(w*128))
    (x : Point) : lookup w a x.val = flatLookup w code x.val := by
  have hx : x.val / 128 < 189 := by omega
  unfold lookup flatLookup
  rw [h ⟨x.val / 128, hx⟩]
  rw [digit_mod _ _ _ _ (by have hm := Nat.mod_lt x.val (by decide : 0 < 128); nlinarith)]
  rw [← Nat.shiftRight_add]
  congr 2
  have hd := Nat.div_add_mod x.val 128
  nlinarith

theorem map_eq (code : Nat) {n : Nat} (f : Fin n → Nat)
    (h : ∀ i, f i = (code >>> (700*i.val)) % 2^700)
    (i : Fin n) (x : Fin 100) :
    fastMap code i.val x.val = (packedMap (f i) x).val := by
  unfold fastMap packedMap
  rw [h i]
  have he : 7 * (100*i.val+x.val) = 700*i.val + 7*x.val := by omega
  rw [he, Nat.shiftRight_add]
  exact congrArg (· % 100)
    (digit_mod (code >>> (700*i.val)) (7*x.val) 700 7
      (by have := x.isLt; omega)).symm

theorem rep0_codes : ∀ i : Fin 100,
    rep0Code i = (flatRep0 >>> (700*i.val)) % 2^700 := by
  apply allFin
  decide +kernel
theorem rep1_codes : ∀ i : Fin 63,
    rep1Code i = (flatRep1 >>> (700*i.val)) % 2^700 := by
  apply allFin
  decide +kernel
theorem rep2_codes : ∀ i : Fin 24,
    rep2Code i = (flatRep2 >>> (700*i.val)) % 2^700 := by
  apply allFin
  decide +kernel
theorem rep3_codes : ∀ i : Fin 4,
    rep3Code i = (flatRep3 >>> (700*i.val)) % 2^700 := by
  apply allFin
  decide +kernel

theorem fastMap_rep0 (i : Fin 100) (x : Fin 100) :
    fastMap flatRep0 i.val x.val = (rep0 i x).val := map_eq _ _ rep0_codes i x
theorem fastMap_rep1 (i : Fin 63) (x : Fin 100) :
    fastMap flatRep1 i.val x.val = (rep1 i x).val := map_eq _ _ rep1_codes i x
theorem fastMap_rep2 (i : Fin 24) (x : Fin 100) :
    fastMap flatRep2 i.val x.val = (rep2 i x).val := map_eq _ _ rep2_codes i x
theorem fastMap_rep3 (i : Fin 4) (x : Fin 100) :
    fastMap flatRep3 i.val x.val = (rep3 i x).val := map_eq _ _ rep3_codes i x

def decode (n : Nat) : Index :=
  (⟨n % 100, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 100 % 63, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 6300 % 24, Nat.mod_lt _ (by decide)⟩,
    ⟨n / 151200 % 4, Nat.mod_lt _ (by decide)⟩)

theorem fastNormal_eq (n : Nat) (x : Fin 100) :
    fastNormal n x.val = (normalForm (decode n) x).val := by
  simp only [normalForm, Equiv.Perm.mul_apply,
    ← fastMap_rep0, ← fastMap_rep1, ← fastMap_rep2, ← fastMap_rep3]
  rfl

theorem fastMap_power : ∀ u v : Fin 5, ∀ x : Fin 100,
    fastMap flatPowerMap (u.val+5*v.val) x.val =
      ((leftTable^u.val * rightTable^v.val) x).val := by
  apply allFin
  decide +kernel

theorem letter_base : ∀ l j : Fin 4,
    flatLookup 7 flatLetterBase (4*l.val+j.val) % 100 =
      (tableLetter l (basePoint j)).val := by
  decide +kernel

theorem normalFormCodes_blocks : ∀ i : Fin 189,
    normalFormCodes[i.val]! = (flatnormalFormCodes >>> (20*128*i.val)) % 2^(20*128) := by
  apply allFin
  decide +kernel

theorem normalFormCodes_lookup (x : Point) :
    lookup 20 normalFormCodes x.val = flatLookup 20 flatnormalFormCodes x.val :=
  flatLookup_eq _ _ _ normalFormCodes_blocks x

theorem actionA_blocks : ∀ i : Fin 189,
    actionA[i.val]! = (flatactionA >>> (15*128*i.val)) % 2^(15*128) := by
  apply allFin
  decide +kernel

theorem actionA_lookup (x : Point) :
    lookup 15 actionA x.val = flatLookup 15 flatactionA x.val :=
  flatLookup_eq _ _ _ actionA_blocks x

theorem actionB_blocks : ∀ i : Fin 189,
    actionB[i.val]! = (flatactionB >>> (15*128*i.val)) % 2^(15*128) := by
  apply allFin
  decide +kernel

theorem actionB_lookup (x : Point) :
    lookup 15 actionB x.val = flatLookup 15 flatactionB x.val :=
  flatLookup_eq _ _ _ actionB_blocks x

theorem actionBInv_blocks : ∀ i : Fin 189,
    actionBInv[i.val]! = (flatactionBInv >>> (15*128*i.val)) % 2^(15*128) := by
  apply allFin
  decide +kernel

theorem actionBInv_lookup (x : Point) :
    lookup 15 actionBInv x.val = flatLookup 15 flatactionBInv x.val :=
  flatLookup_eq _ _ _ actionBInv_blocks x

theorem edgePowersA_blocks : ∀ i : Fin 189,
    edgePowersA[i.val]! = (flatedgePowersA >>> (5*128*i.val)) % 2^(5*128) := by
  apply allFin
  decide +kernel

theorem edgePowersA_lookup (x : Point) :
    lookup 5 edgePowersA x.val = flatLookup 5 flatedgePowersA x.val :=
  flatLookup_eq _ _ _ edgePowersA_blocks x

theorem edgePowersB_blocks : ∀ i : Fin 189,
    edgePowersB[i.val]! = (flatedgePowersB >>> (5*128*i.val)) % 2^(5*128) := by
  apply allFin
  decide +kernel

theorem edgePowersB_lookup (x : Point) :
    lookup 5 edgePowersB x.val = flatLookup 5 flatedgePowersB x.val :=
  flatLookup_eq _ _ _ edgePowersB_blocks x

theorem edgePowersBInv_blocks : ∀ i : Fin 189,
    edgePowersBInv[i.val]! = (flatedgePowersBInv >>> (5*128*i.val)) % 2^(5*128) := by
  apply allFin
  decide +kernel

theorem edgePowersBInv_lookup (x : Point) :
    lookup 5 edgePowersBInv x.val = flatLookup 5 flatedgePowersBInv x.val :=
  flatLookup_eq _ _ _ edgePowersBInv_blocks x

theorem candidateIndex_eq (x : Point) :
    candidateIndex x = decode (flatLookup 20 flatnormalFormCodes x.val) := by
  simp only [candidateIndex, decode, normalFormCodes_lookup]

theorem fastAction_eq (l : Fin 4) (x : Point) :
    fastAction l.val x.val = (step l x).val := by
  fin_cases l <;> simp [fastAction, step, actionA_lookup, actionB_lookup, actionBInv_lookup]

theorem fastPower_eq (l : Fin 4) (x : Point) :
    (edgePowers x l).1.val = fastPower l.val x.val % 5 ∧
    (edgePowers x l).2.val = fastPower l.val x.val / 5 % 5 := by
  fin_cases l <;> simp [fastPower, edgePowers, edgePowersA_lookup,
    edgePowersB_lookup, edgePowersBInv_lookup]

theorem edge_of_raw (x : Point) (l j : Fin 4) (h : rawEdge x.val l.val j.val) :
    normalForm (candidateIndex x) (tableLetter l (basePoint j)) =
      (leftTable ^ (edgePowers x l).1.val * rightTable ^ (edgePowers x l).2.val)
        (normalForm (candidateIndex (step l x)) (basePoint j)) := by
  apply Fin.ext
  unfold rawEdge at h
  have hj (n : Nat) : fastNormal n j.val = (normalForm (decode n) (basePoint j)).val :=
    fastNormal_eq n (basePoint j)
  rw [letter_base, fastAction_eq, fastNormal_eq _ (tableLetter l (basePoint j)), hj] at h
  rw [← candidateIndex_eq, ← candidateIndex_eq] at h
  rw [← (fastPower_eq l x).1, ← (fastPower_eq l x).2, fastMap_power] at h
  exact h

/-- Force one natural-number computation before reusing it. The cases only
control kernel evaluation; `bindNat_eq` gives its ordinary mathematical value. -/
def bindNat {α : Sort*} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

theorem bindNat_eq {α : Sort*} (n : Nat) (f : Nat → α) : bindNat n f = f n := by
  cases n <;> rfl

/-- Check all four base points after decoding this edge's row data once. -/
def fastCheck (x l : Nat) : Bool :=
  bindNat (flatLookup 20 flatnormalFormCodes x) fun n =>
  bindNat (fastAction l x) fun y =>
  bindNat (flatLookup 20 flatnormalFormCodes y) fun m =>
  bindNat (fastPower l x) fun p =>
  (List.range 4).all fun j =>
    fastNormal n (flatLookup 7 flatLetterBase (4*l+j) % 100) ==
      fastMap flatPowerMap (p%5+5*(p/5%5)) (fastNormal m j)

theorem fastCheck_sound (x l : Nat) (h : fastCheck x l = true) (j : Fin 4) :
    rawEdge x l j.val := by
  unfold fastCheck at h
  simp only [bindNat_eq] at h
  exact beq_iff_eq.mp (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt))

/-- One bounded block, including the repeated involutory letter 2. -/
def checkBlock (b : Nat) : Bool :=
  (List.range 128).all fun i =>
    (List.range 4).all fun l => fastCheck (128*b+i) l

theorem checkBlock_sound (b : Nat) (h : checkBlock b = true)
    (i : Fin 128) (l j : Fin 4) : rawEdge (128*b+i.val) l.val j.val := by
  apply fastCheck_sound _ _ _ j
  exact List.all_eq_true.mp
    (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
    l.val (List.mem_range.mpr l.isLt)
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry.Edges
