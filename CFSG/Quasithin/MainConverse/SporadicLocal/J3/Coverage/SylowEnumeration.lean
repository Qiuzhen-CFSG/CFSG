module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Representatives

/-!
# Enumerating the fixed Sylow candidate by a free point orbit

The 128 short words below have distinct images of letter 0. Hence they
exhaust the fixed Sylow candidate if its order is 128. Evaluation at that
single letter is then injective on the whole subgroup. Subsequent finite
calculations can use this injectivity to certify equalities without comparing
6156 letters each time.

Source: the fixed ATLAS words in TwoLocal/Generators.lean; the enumeration
was discovered from those words and every point image is kernel checked here.
This does not assert the Sylow order or elementary-subgroup fusion.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal
open Theory.GroupTheory Sporadic.Janko3.OrderCertificate
set_option maxRecDepth 40000
set_option Elab.async false

/-- Short words in the five fixed Sylow generators. -/
@[expose] public def sylowEnumerationWord : Fin 128 → List (Fin 5)
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [4]
  | 6 => [0, 1]
  | 7 => [0, 2]
  | 8 => [0, 3]
  | 9 => [0, 4]
  | 10 => [1, 2]
  | 11 => [1, 3]
  | 12 => [1, 4]
  | 13 => [2, 1]
  | 14 => [2, 3]
  | 15 => [2, 4]
  | 16 => [3, 1]
  | 17 => [3, 2]
  | 18 => [3, 4]
  | 19 => [4, 1]
  | 20 => [4, 2]
  | 21 => [4, 3]
  | 22 => [0, 1, 2]
  | 23 => [0, 1, 3]
  | 24 => [0, 1, 4]
  | 25 => [0, 2, 1]
  | 26 => [0, 2, 4]
  | 27 => [0, 3, 1]
  | 28 => [0, 3, 4]
  | 29 => [0, 4, 1]
  | 30 => [0, 4, 2]
  | 31 => [0, 4, 3]
  | 32 => [1, 2, 1]
  | 33 => [1, 2, 3]
  | 34 => [1, 2, 4]
  | 35 => [1, 3, 1]
  | 36 => [1, 3, 2]
  | 37 => [1, 3, 4]
  | 38 => [1, 4, 1]
  | 39 => [1, 4, 2]
  | 40 => [1, 4, 3]
  | 41 => [2, 1, 2]
  | 42 => [2, 1, 3]
  | 43 => [2, 1, 4]
  | 44 => [2, 3, 1]
  | 45 => [2, 3, 4]
  | 46 => [2, 4, 1]
  | 47 => [2, 4, 2]
  | 48 => [2, 4, 3]
  | 49 => [3, 1, 2]
  | 50 => [3, 1, 3]
  | 51 => [3, 2, 1]
  | 52 => [3, 2, 4]
  | 53 => [3, 4, 1]
  | 54 => [3, 4, 2]
  | 55 => [3, 4, 3]
  | 56 => [4, 1, 2]
  | 57 => [4, 1, 4]
  | 58 => [4, 2, 1]
  | 59 => [4, 2, 3]
  | 60 => [4, 3, 1]
  | 61 => [4, 3, 2]
  | 62 => [4, 3, 4]
  | 63 => [0, 1, 2, 4]
  | 64 => [0, 1, 3, 1]
  | 65 => [0, 1, 3, 4]
  | 66 => [0, 1, 4, 1]
  | 67 => [0, 1, 4, 2]
  | 68 => [0, 2, 1, 2]
  | 69 => [0, 2, 1, 3]
  | 70 => [0, 2, 4, 1]
  | 71 => [0, 2, 4, 2]
  | 72 => [0, 2, 4, 3]
  | 73 => [0, 3, 1, 2]
  | 74 => [0, 3, 1, 3]
  | 75 => [0, 3, 4, 2]
  | 76 => [0, 3, 4, 3]
  | 77 => [0, 4, 1, 4]
  | 78 => [0, 4, 2, 1]
  | 79 => [0, 4, 3, 1]
  | 80 => [1, 2, 1, 2]
  | 81 => [1, 2, 1, 3]
  | 82 => [1, 2, 3, 1]
  | 83 => [1, 2, 3, 4]
  | 84 => [1, 2, 4, 1]
  | 85 => [1, 2, 4, 2]
  | 86 => [1, 2, 4, 3]
  | 87 => [1, 3, 1, 2]
  | 88 => [1, 3, 1, 3]
  | 89 => [1, 3, 2, 1]
  | 90 => [1, 3, 2, 4]
  | 91 => [1, 3, 4, 1]
  | 92 => [1, 3, 4, 2]
  | 93 => [1, 3, 4, 3]
  | 94 => [1, 4, 1, 2]
  | 95 => [1, 4, 1, 4]
  | 96 => [1, 4, 2, 1]
  | 97 => [1, 4, 2, 3]
  | 98 => [1, 4, 3, 1]
  | 99 => [1, 4, 3, 2]
  | 100 => [2, 1, 2, 1]
  | 101 => [2, 1, 2, 3]
  | 102 => [2, 1, 3, 1]
  | 103 => [2, 1, 3, 2]
  | 104 => [2, 1, 4, 1]
  | 105 => [2, 3, 1, 2]
  | 106 => [2, 3, 1, 3]
  | 107 => [2, 4, 1, 4]
  | 108 => [2, 4, 2, 3]
  | 109 => [3, 1, 2, 1]
  | 110 => [3, 1, 2, 4]
  | 111 => [3, 1, 3, 1]
  | 112 => [3, 1, 3, 2]
  | 113 => [3, 1, 3, 4]
  | 114 => [3, 2, 1, 2]
  | 115 => [3, 2, 1, 3]
  | 116 => [3, 2, 4, 2]
  | 117 => [0, 1, 2, 4, 3]
  | 118 => [0, 1, 3, 4, 3]
  | 119 => [0, 1, 4, 1, 4]
  | 120 => [1, 2, 1, 2, 3]
  | 121 => [1, 2, 1, 3, 2]
  | 122 => [1, 2, 3, 1, 2]
  | 123 => [1, 2, 3, 1, 3]
  | 124 => [1, 2, 4, 1, 4]
  | 125 => [1, 3, 1, 3, 2]
  | 126 => [1, 3, 2, 1, 2]
  | _ => [1, 3, 2, 1, 3]

/-- Evaluation of a positive word stays in the fixed Sylow candidate. -/
@[expose] public def sylowWordElement (w : List (Fin 5)) : sylowCandidate :=
  ⟨evalWord sylowGenerator w, by
    induction w with
    | nil => exact sylowCandidate.one_mem
    | cons i w ih => exact sylowCandidate.mul_mem (sylowGenerator_mem i) ih⟩

/-- The 128 model elements selected by the short words. -/
@[expose] public def sylowEnumeration (i : Fin 128) : sylowCandidate :=
  sylowWordElement (sylowEnumerationWord i)

/-- The distinct images of letter 0, in enumeration order. -/
@[expose] public def sylowEnumerationPoint : Fin 128 → Fin 6156
  | 0 => 0
  | 1 => 2786
  | 2 => 4624
  | 3 => 349
  | 4 => 399
  | 5 => 737
  | 6 => 849
  | 7 => 5128
  | 8 => 1105
  | 9 => 4992
  | 10 => 5533
  | 11 => 3023
  | 12 => 2291
  | 13 => 5900
  | 14 => 1282
  | 15 => 2248
  | 16 => 2382
  | 17 => 1411
  | 18 => 5695
  | 19 => 2375
  | 20 => 5126
  | 21 => 5007
  | 22 => 5550
  | 23 => 384
  | 24 => 2213
  | 25 => 2605
  | 26 => 2011
  | 27 => 2591
  | 28 => 4600
  | 29 => 2796
  | 30 => 1036
  | 31 => 3076
  | 32 => 3633
  | 33 => 433
  | 34 => 4201
  | 35 => 41
  | 36 => 141
  | 37 => 471
  | 38 => 1439
  | 39 => 3615
  | 40 => 332
  | 41 => 538
  | 42 => 4966
  | 43 => 2666
  | 44 => 4655
  | 45 => 2303
  | 46 => 4945
  | 47 => 4097
  | 48 => 3614
  | 49 => 1910
  | 50 => 5442
  | 51 => 1259
  | 52 => 4849
  | 53 => 2609
  | 54 => 3775
  | 55 => 3621
  | 56 => 3033
  | 57 => 712
  | 58 => 3236
  | 59 => 570
  | 60 => 3372
  | 61 => 4238
  | 62 => 3660
  | 63 => 3567
  | 64 => 2264
  | 65 => 214
  | 66 => 3185
  | 67 => 2
  | 68 => 713
  | 69 => 5354
  | 70 => 3186
  | 71 => 2061
  | 72 => 6035
  | 73 => 537
  | 74 => 3058
  | 75 => 5041
  | 76 => 3155
  | 77 => 3945
  | 78 => 4625
  | 79 => 2665
  | 80 => 5098
  | 81 => 145
  | 82 => 548
  | 83 => 4163
  | 84 => 1818
  | 85 => 5351
  | 86 => 3807
  | 87 => 2950
  | 88 => 144
  | 89 => 730
  | 90 => 1532
  | 91 => 1167
  | 92 => 5321
  | 93 => 5718
  | 94 => 2163
  | 95 => 5257
  | 96 => 3984
  | 97 => 4187
  | 98 => 1028
  | 99 => 2782
  | 100 => 3662
  | 101 => 911
  | 102 => 2569
  | 103 => 149
  | 104 => 3694
  | 105 => 495
  | 106 => 2676
  | 107 => 1022
  | 108 => 312
  | 109 => 603
  | 110 => 2693
  | 111 => 898
  | 112 => 6081
  | 113 => 770
  | 114 => 650
  | 115 => 2604
  | 116 => 4373
  | 117 => 3081
  | 118 => 2715
  | 119 => 5713
  | 120 => 2025
  | 121 => 629
  | 122 => 5716
  | 123 => 5080
  | 124 => 3258
  | 125 => 4693
  | 126 => 4538
  | _ => 1290

private def fastSylowGenerator (i : Fin 5) : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (sylowWord0 i) * evalWord L1Gen (sylowWord1 i) *
    evalWord L2Gen (sylowWord2 i)

private theorem fastSylowGenerator_eq (i : Fin 5) :
    fastSylowGenerator i = embedding (sylowGenerator i) := by
  rw [fastSylowGenerator, fastL0Gen_eq]
  rfl

private theorem fastSylowWord_eq (w : List (Fin 5)) :
    evalWord fastSylowGenerator w = embedding (sylowWordElement w) := by
  change evalWord fastSylowGenerator w = embedding (evalWord sylowGenerator w)
  induction w with
  | nil => exact (map_one embedding).symm
  | cons i w ih =>
    simp only [evalWord, map_mul, ← fastSylowGenerator_eq, ← ih]

set_option maxHeartbeats 4000000 in
/-- Each tabulated point is the actual image under the corresponding model word. -/
public theorem sylowEnumeration_point (i : Fin 128) :
    embedding (sylowEnumeration i) 0 = sylowEnumerationPoint i := by
  have h : ∀ j : Fin 128,
      (evalWord fastSylowGenerator (sylowEnumerationWord j)) 0 =
        sylowEnumerationPoint j := by
    apply allFin
    decide +kernel
  simpa only [fastSylowWord_eq, sylowEnumeration] using h i

public theorem sylowEnumerationPoint_injective :
    Function.Injective sylowEnumerationPoint := by decide +kernel

public theorem sylowEnumeration_injective : Function.Injective sylowEnumeration := by
  intro i j hij
  apply sylowEnumerationPoint_injective
  simpa only [sylowEnumeration_point] using
    congrArg (fun x : sylowCandidate => embedding (x : Model) 0) hij

/-- The numerical order premise makes the explicit enumeration exhaustive. -/
public theorem sylowEnumeration_surjective (hS : Nat.card sylowCandidate = 128) :
    Function.Surjective sylowEnumeration := by
  apply (sylowEnumeration_injective.bijective_of_nat_card_le _).2
  rw [hS, Nat.card_fin]

/-- One letter separates all elements of the fixed Sylow candidate. -/
public theorem sylowCandidate_point_injective (hS : Nat.card sylowCandidate = 128) :
    Function.Injective (fun x : sylowCandidate => embedding (x : Model) 0) := by
  intro x y hxy
  obtain ⟨i, rfl⟩ := sylowEnumeration_surjective hS x
  obtain ⟨j, rfl⟩ := sylowEnumeration_surjective hS y
  change embedding (sylowEnumeration i) 0 = embedding (sylowEnumeration j) 0 at hxy
  rw [sylowEnumeration_point, sylowEnumeration_point] at hxy
  exact congrArg sylowEnumeration (sylowEnumerationPoint_injective hxy)

/-- Equality in the fixed Sylow candidate reduces to one point image. -/
public theorem sylowCandidate_eq_of_point_eq (hS : Nat.card sylowCandidate = 128)
    {x y : Model} (hx : x ∈ sylowCandidate) (hy : y ∈ sylowCandidate)
    (hxy : embedding x 0 = embedding y 0) : x = y :=
  congrArg Subtype.val (sylowCandidate_point_injective hS
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

/-- Positions of the four published elementary generators in the enumeration. -/
@[expose] public def elementaryGeneratorIndex : Fin 4 → Fin 128
  | 0 => 1
  | 1 => 5
  | 2 => 95
  | 3 => 41

private def fastElementaryGenerator (i : Fin 4) : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (elementaryWord0 i) * evalWord L1Gen (elementaryWord1 i) *
    evalWord L2Gen (elementaryWord2 i)

private theorem fastElementaryGenerator_eq (i : Fin 4) :
    fastElementaryGenerator i = embedding (elementaryGenerator i) := by
  rw [fastElementaryGenerator, fastL0Gen_eq]
  rfl

private def elementaryWordBlock (i : Fin 4) (b : Fin 43) : Bool :=
  checkFin (fun k : Fin 144 =>
    if h : b.val * 144 + k.val < 6156 then
      decide (fastElementaryGenerator i ⟨b.val * 144 + k.val, h⟩ =
        (evalWord fastSylowGenerator (sylowEnumerationWord (elementaryGeneratorIndex i)))
          ⟨b.val * 144 + k.val, h⟩)
    else true)

private theorem elementaryGenerator_word_of_blocks (i : Fin 4)
    (h : ∀ b : Fin 43, elementaryWordBlock i b = true) :
    fastElementaryGenerator i =
      evalWord fastSylowGenerator (sylowEnumerationWord (elementaryGeneratorIndex i)) := by
  apply Equiv.ext
  intro x
  let b : Fin 43 := ⟨x.val / 144, by have := x.isLt; omega⟩
  let k : Fin 144 := ⟨x.val % 144, Nat.mod_lt _ (by decide)⟩
  have heq : b.val * 144 + k.val = x.val := by
    dsimp [b, k]
    omega
  have hh : b.val * 144 + k.val < 6156 := by rw [heq]; exact x.isLt
  have hb := List.all_eq_true.mp (h b) k.val (List.mem_range.mpr k.isLt)
  dsimp [elementaryWordBlock, checkFin] at hb
  simp only [if_pos k.isLt, dif_pos hh, decide_eq_true_eq] at hb
  simpa only [Fin.ext_iff, heq] using hb

private theorem elementaryWordBlock_2_00 : elementaryWordBlock 2 0 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_01 : elementaryWordBlock 2 1 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_02 : elementaryWordBlock 2 2 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_03 : elementaryWordBlock 2 3 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_04 : elementaryWordBlock 2 4 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_05 : elementaryWordBlock 2 5 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_06 : elementaryWordBlock 2 6 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_07 : elementaryWordBlock 2 7 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_08 : elementaryWordBlock 2 8 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_09 : elementaryWordBlock 2 9 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_10 : elementaryWordBlock 2 10 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_11 : elementaryWordBlock 2 11 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_12 : elementaryWordBlock 2 12 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_13 : elementaryWordBlock 2 13 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_14 : elementaryWordBlock 2 14 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_15 : elementaryWordBlock 2 15 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_16 : elementaryWordBlock 2 16 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_17 : elementaryWordBlock 2 17 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_18 : elementaryWordBlock 2 18 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_19 : elementaryWordBlock 2 19 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_20 : elementaryWordBlock 2 20 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_21 : elementaryWordBlock 2 21 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_22 : elementaryWordBlock 2 22 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_23 : elementaryWordBlock 2 23 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_24 : elementaryWordBlock 2 24 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_25 : elementaryWordBlock 2 25 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_26 : elementaryWordBlock 2 26 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_27 : elementaryWordBlock 2 27 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_28 : elementaryWordBlock 2 28 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_29 : elementaryWordBlock 2 29 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_30 : elementaryWordBlock 2 30 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_31 : elementaryWordBlock 2 31 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_32 : elementaryWordBlock 2 32 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_33 : elementaryWordBlock 2 33 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_34 : elementaryWordBlock 2 34 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_35 : elementaryWordBlock 2 35 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_36 : elementaryWordBlock 2 36 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_37 : elementaryWordBlock 2 37 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_38 : elementaryWordBlock 2 38 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_39 : elementaryWordBlock 2 39 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_40 : elementaryWordBlock 2 40 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_41 : elementaryWordBlock 2 41 = true := by
  decide +kernel

private theorem elementaryWordBlock_2_42 : elementaryWordBlock 2 42 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_00 : elementaryWordBlock 3 0 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_01 : elementaryWordBlock 3 1 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_02 : elementaryWordBlock 3 2 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_03 : elementaryWordBlock 3 3 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_04 : elementaryWordBlock 3 4 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_05 : elementaryWordBlock 3 5 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_06 : elementaryWordBlock 3 6 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_07 : elementaryWordBlock 3 7 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_08 : elementaryWordBlock 3 8 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_09 : elementaryWordBlock 3 9 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_10 : elementaryWordBlock 3 10 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_11 : elementaryWordBlock 3 11 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_12 : elementaryWordBlock 3 12 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_13 : elementaryWordBlock 3 13 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_14 : elementaryWordBlock 3 14 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_15 : elementaryWordBlock 3 15 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_16 : elementaryWordBlock 3 16 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_17 : elementaryWordBlock 3 17 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_18 : elementaryWordBlock 3 18 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_19 : elementaryWordBlock 3 19 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_20 : elementaryWordBlock 3 20 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_21 : elementaryWordBlock 3 21 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_22 : elementaryWordBlock 3 22 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_23 : elementaryWordBlock 3 23 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_24 : elementaryWordBlock 3 24 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_25 : elementaryWordBlock 3 25 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_26 : elementaryWordBlock 3 26 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_27 : elementaryWordBlock 3 27 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_28 : elementaryWordBlock 3 28 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_29 : elementaryWordBlock 3 29 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_30 : elementaryWordBlock 3 30 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_31 : elementaryWordBlock 3 31 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_32 : elementaryWordBlock 3 32 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_33 : elementaryWordBlock 3 33 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_34 : elementaryWordBlock 3 34 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_35 : elementaryWordBlock 3 35 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_36 : elementaryWordBlock 3 36 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_37 : elementaryWordBlock 3 37 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_38 : elementaryWordBlock 3 38 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_39 : elementaryWordBlock 3 39 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_40 : elementaryWordBlock 3 40 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_41 : elementaryWordBlock 3 41 = true := by
  decide +kernel

private theorem elementaryWordBlock_3_42 : elementaryWordBlock 3 42 = true := by
  decide +kernel

private theorem elementaryGenerator_word_check (i : Fin 4) :
    fastElementaryGenerator i =
      evalWord fastSylowGenerator (sylowEnumerationWord (elementaryGeneratorIndex i)) := by
  fin_cases i
  · rfl
  · rfl
  · apply elementaryGenerator_word_of_blocks 2
    intro b
    fin_cases b
    · exact elementaryWordBlock_2_00
    · exact elementaryWordBlock_2_01
    · exact elementaryWordBlock_2_02
    · exact elementaryWordBlock_2_03
    · exact elementaryWordBlock_2_04
    · exact elementaryWordBlock_2_05
    · exact elementaryWordBlock_2_06
    · exact elementaryWordBlock_2_07
    · exact elementaryWordBlock_2_08
    · exact elementaryWordBlock_2_09
    · exact elementaryWordBlock_2_10
    · exact elementaryWordBlock_2_11
    · exact elementaryWordBlock_2_12
    · exact elementaryWordBlock_2_13
    · exact elementaryWordBlock_2_14
    · exact elementaryWordBlock_2_15
    · exact elementaryWordBlock_2_16
    · exact elementaryWordBlock_2_17
    · exact elementaryWordBlock_2_18
    · exact elementaryWordBlock_2_19
    · exact elementaryWordBlock_2_20
    · exact elementaryWordBlock_2_21
    · exact elementaryWordBlock_2_22
    · exact elementaryWordBlock_2_23
    · exact elementaryWordBlock_2_24
    · exact elementaryWordBlock_2_25
    · exact elementaryWordBlock_2_26
    · exact elementaryWordBlock_2_27
    · exact elementaryWordBlock_2_28
    · exact elementaryWordBlock_2_29
    · exact elementaryWordBlock_2_30
    · exact elementaryWordBlock_2_31
    · exact elementaryWordBlock_2_32
    · exact elementaryWordBlock_2_33
    · exact elementaryWordBlock_2_34
    · exact elementaryWordBlock_2_35
    · exact elementaryWordBlock_2_36
    · exact elementaryWordBlock_2_37
    · exact elementaryWordBlock_2_38
    · exact elementaryWordBlock_2_39
    · exact elementaryWordBlock_2_40
    · exact elementaryWordBlock_2_41
    · exact elementaryWordBlock_2_42
  · apply elementaryGenerator_word_of_blocks 3
    intro b
    fin_cases b
    · exact elementaryWordBlock_3_00
    · exact elementaryWordBlock_3_01
    · exact elementaryWordBlock_3_02
    · exact elementaryWordBlock_3_03
    · exact elementaryWordBlock_3_04
    · exact elementaryWordBlock_3_05
    · exact elementaryWordBlock_3_06
    · exact elementaryWordBlock_3_07
    · exact elementaryWordBlock_3_08
    · exact elementaryWordBlock_3_09
    · exact elementaryWordBlock_3_10
    · exact elementaryWordBlock_3_11
    · exact elementaryWordBlock_3_12
    · exact elementaryWordBlock_3_13
    · exact elementaryWordBlock_3_14
    · exact elementaryWordBlock_3_15
    · exact elementaryWordBlock_3_16
    · exact elementaryWordBlock_3_17
    · exact elementaryWordBlock_3_18
    · exact elementaryWordBlock_3_19
    · exact elementaryWordBlock_3_20
    · exact elementaryWordBlock_3_21
    · exact elementaryWordBlock_3_22
    · exact elementaryWordBlock_3_23
    · exact elementaryWordBlock_3_24
    · exact elementaryWordBlock_3_25
    · exact elementaryWordBlock_3_26
    · exact elementaryWordBlock_3_27
    · exact elementaryWordBlock_3_28
    · exact elementaryWordBlock_3_29
    · exact elementaryWordBlock_3_30
    · exact elementaryWordBlock_3_31
    · exact elementaryWordBlock_3_32
    · exact elementaryWordBlock_3_33
    · exact elementaryWordBlock_3_34
    · exact elementaryWordBlock_3_35
    · exact elementaryWordBlock_3_36
    · exact elementaryWordBlock_3_37
    · exact elementaryWordBlock_3_38
    · exact elementaryWordBlock_3_39
    · exact elementaryWordBlock_3_40
    · exact elementaryWordBlock_3_41
    · exact elementaryWordBlock_3_42

/-- Each fixed elementary generator is an explicitly enumerated Sylow word.
Unlike exhaustiveness, these identities use no cardinality hypothesis. -/
public theorem elementaryGenerator_eq_sylowEnumeration (i : Fin 4) :
    elementaryGenerator i = (sylowEnumeration (elementaryGeneratorIndex i) : Model) := by
  apply embedding_injective
  rw [← fastElementaryGenerator_eq, sylowEnumeration, ← fastSylowWord_eq]
  exact elementaryGenerator_word_check i

/-- The fixed elementary candidate is contained in the fixed Sylow candidate. -/
public theorem elementaryCandidate_le_sylowCandidate : elementaryCandidate ≤ sylowCandidate := by
  apply (closure_le _).mpr
  rintro x ⟨i, rfl⟩
  rw [elementaryGenerator_eq_sylowEnumeration]
  exact (sylowEnumeration (elementaryGeneratorIndex i)).property

/-- All five fixed representatives lie in the Sylow candidate. -/
public theorem elementaryRepresentative_le_sylowCandidate (i : Fin 5) :
    elementaryRepresentative i ≤ sylowCandidate :=
  (elementaryRepresentative_le_elementaryCandidate i).trans elementaryCandidate_le_sylowCandidate

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
