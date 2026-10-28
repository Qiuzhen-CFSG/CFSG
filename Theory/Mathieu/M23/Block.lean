module

public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic.FinCases
public import Mathlib.Data.Nat.Count
public import Theory.Mathieu.M24.Block

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The 253 W23 heptads as compact 23-bit incidence masks. -/
@[expose]
public noncomputable def m23BlockMaskArray : Array Nat := #[
  133182, 541262, 1085582, 2367758, 4260879, 1057878, 4472982, 594198,
  2130455, 487, 267814, 4759590, 3227686, 362566, 6426694, 205446,
  2624646, 5245702, 181510, 30727, 1966087, 2162906, 1065243, 4207130,
  820250, 5505130, 25770, 99114, 2625579, 7498, 172107, 4850058,
  264843, 3278346, 1648650, 6342666, 479242, 53362, 1573554, 6292786,
  335923, 394066, 4720723, 43410, 136339, 85522, 3414034, 2777106,
  5472274, 2108002, 722018, 4266146, 2523298, 805154, 1192226, 4342307,
  1084451, 4228802, 1198274, 798914, 4284738, 3703106, 1118787, 2376771,
  2118530, 1377666, 7348355, 639107, 534275, 2296067, 4493571, 694786,
  1368578, 7143938, 4598786, 2208770, 5788674, 4227420, 532637, 1376796,
  2118684, 77932, 6292140, 1574188, 311341, 394444, 3147853, 84364,
  135949, 44556, 4986892, 5398540, 2850828, 2883700, 99508, 25396,
  5247029, 6868, 213077, 3277204, 265493, 4851220, 6367252, 1624084,
  438292, 1213028, 4213860, 1321124, 676004, 2136356, 4653348, 592421,
  2237477, 2154692, 5832900, 2164548, 665924, 1331524, 4465221, 562245,
  820100, 4208004, 1066629, 4360325, 2429061, 1155333, 6832389, 2509316,
  3682820, 4313604, 1252356, 877572, 7635972, 1657, 266680, 3186744,
  4800568, 288856, 1708120, 180888, 5246104, 2624280, 206104, 104473,
  6684697, 559336, 2244968, 1245353, 4204841, 1071656, 926248, 2427944,
  4363304, 1057736, 4214985, 852297, 4393544, 2396744, 6825032, 1164360,
  2131337, 595592, 2242696, 4563080, 3948680, 4474632, 1476872, 585992,
  7409928, 2187785, 5800457, 674825, 1324041, 4333808, 1116528, 2115761,
  688433, 4491824, 2298416, 539696, 1459248, 542160, 1343697, 2109777,
  631376, 7357008, 2264144, 4527184, 4260753, 2369168, 985232, 1142928,
  6852752, 1087248, 4348176, 6037776, 2474256, 1190417, 807441, 4252689,
  3736593, 344800, 3151072, 4723552, 304480, 399457, 1597537, 6389857,
  135072, 2695584, 5292448, 45729, 4981921, 3408673, 87329, 5318176,
  2672160, 256032, 7997472, 6582304, 1937440, 6556096, 233920, 2753217,
  76993, 52033, 5375297, 1838656, 161344, 5290048, 2709568, 3612736,
  5161024, 1579393, 418177, 4745856, 3246720, 5640832, 318592, 1746048,
  6505600, 342784, 6464256, 1786624, 3173632, 4820224, 3020032, 6299137,
  493057, 2926593, 5588993, 4927489, 3330049
]

public theorem m23BlockMaskArray_size : m23BlockMaskArray.size = 253 := by decide +kernel

@[expose]
public noncomputable def m23BlockMask (i : Fin 253) : Nat :=
  m23BlockMaskArray[i.val]'(by rw [m23BlockMaskArray_size]; exact i.isLt)

/-- Decode a 23-bit incidence mask into a point set. -/
@[expose]
public noncomputable def m23MaskBlock (mask : Nat) : Finset (Fin 23) :=
  Finset.univ.filter (fun x => mask.testBit x.val = true)

/-- Decode the mask with the given certificate index. -/
@[expose]
public noncomputable def m23BlockAt (i : Fin 253) : Finset (Fin 23) :=
  m23MaskBlock (m23BlockMask i)

public theorem m23BlockAt_card : ∀ i, (m23BlockAt i).card = 7 := by decide +kernel

/-- The explicit finite set of all 253 heptads. -/
@[expose]
public noncomputable def m23Blocks : Finset (Finset (Fin 23)) :=
  Finset.univ.image m23BlockAt

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Atlas labels 1--23 identified with degree-24 points other than label 24. -/
@[expose] public def m23PointEquiv : Fin 23 ≃ {x : Fin 24 // x ≠ (24 : Fin 24)} :=
  (List.formPerm
    ([0, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8,
      7, 6, 5, 4, 3, 2, 1] : List (Fin 23))).trans
    (finSuccAboveEquiv (24 : Fin 24))

/-- Embed Atlas labels 1--23 into degree 24, omitting label 24. -/
@[expose] public def m23PointEmbedding : Fin 23 ↪ Fin 24 :=
  m23PointEquiv.toEmbedding.trans (Function.Embedding.subtype _)

/-- Numeric normal form of the Atlas-labelled embedding: label 23 is represented
by `0 : Fin 23`, while all other labels retain their numeric value. -/
public theorem m23PointEmbedding_apply (x : Fin 23) :
    m23PointEmbedding x =
      if x = 0 then (23 : Fin 24)
      else Fin.castLE (by decide +kernel : 23 ≤ 24) x := by
  fin_cases x <;> decide +kernel

/-- Lift a W23 block into the Atlas-labelled points 1--23 of Fin 24. -/
@[expose] public def m23LiftBlock (B : Finset (Fin 23)) : Finset (Fin 24) :=
  B.map m23PointEmbedding

/-- Add Atlas point 24 to a lifted W23 heptad. -/
@[expose] public def m23AugmentedBlock (B : Finset (Fin 23)) : Finset (Fin 24) :=
  insert (24 : Fin 24) (m23LiftBlock B)

/-- Exposed computational interface for augmented W23 blocks. -/
public theorem m23AugmentedBlock_eq_insert_map (B : Finset (Fin 23)) :
    m23AugmentedBlock B =
      insert (24 : Fin 24) (B.map m23PointEmbedding) := rfl

public theorem m23LiftBlock_not_mem_24 (B : Finset (Fin 23)) :
    (24 : Fin 24) ∉ m23LiftBlock B := by
  rw [m23LiftBlock, Finset.mem_map]
  rintro ⟨x, -, hx⟩
  change (m23PointEquiv x).1 = (24 : Fin 24) at hx
  exact (m23PointEquiv x).2 hx

public theorem m23AugmentedBlock_inter (B C : Finset (Fin 23)) :
    m23AugmentedBlock B ∩ m23AugmentedBlock C =
      m23AugmentedBlock (B ∩ C) := by
  rw [m23AugmentedBlock, m23AugmentedBlock, m23AugmentedBlock]
  rw [Finset.insert_inter_of_mem (Finset.mem_insert_self _ _)]
  rw [Finset.inter_insert_of_notMem (m23LiftBlock_not_mem_24 B)]
  change
    insert (24 : Fin 24)
        (B.map m23PointEmbedding ∩ C.map m23PointEmbedding) =
      insert (24 : Fin 24) ((B ∩ C).map m23PointEmbedding)
  rw [Finset.map_inter]

public theorem m23AugmentedBlock_card (B : Finset (Fin 23)) :
    (m23AugmentedBlock B).card = B.card + 1 := by
  rw [m23AugmentedBlock,
    Finset.card_insert_of_notMem (m23LiftBlock_not_mem_24 B),
    m23LiftBlock, Finset.card_map]

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Number of common points of two block masks, computed directly on 23 bits. -/
@[expose]
public noncomputable def m23CommonCount (i j : Fin 253) : Nat :=
  (List.range 23).countP
    (fun k => (m23BlockMask i &&& m23BlockMask j).testBit k)

private theorem m23MaskBlock_inter (a b : Nat) :
    m23MaskBlock a ∩ m23MaskBlock b = m23MaskBlock (a &&& b) := by
  apply Finset.ext
  intro x
  simp only [Finset.mem_inter, m23MaskBlock, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Nat.testBit_and]
  simp

private theorem m23MaskBlock_card_eq_count (mask : Nat) :
    (m23MaskBlock mask).card =
      (List.range 23).countP (fun k => mask.testBit k) := by
  calc
    (m23MaskBlock mask).card =
        Nat.count (fun k => mask.testBit k = true) 23 := by
      rw [Nat.count_eq_card_filter_range]
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        simpa [m23MaskBlock] using hx
      · intro a ha b hb h
        exact Fin.ext h
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_range] at hb
        refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
        simpa [m23MaskBlock] using hb.2
    _ = (List.range 23).countP (fun k => mask.testBit k) := by
      simp [Nat.count]

public theorem m23CommonCount_eq_card (i j : Fin 253) :
    m23CommonCount i j = (m23BlockAt i ∩ m23BlockAt j).card := by
  rw [m23BlockAt, m23BlockAt, m23MaskBlock_inter,
    m23MaskBlock_card_eq_count]
  rfl

/-- Increasing list of the positions of the set bits below 23. -/
@[expose]
public def m23MaskPoints (mask : Nat) : List Nat :=
  (List.range 23).filter mask.testBit

/-- Encode a list of point positions as an incidence mask. -/
@[expose]
public def m23Submask (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc ||| 2 ^ x) 0

/-- The masks of the four-point sublists of a seven-point block mask. -/
@[expose]
public def m23FourSubmasks (mask : Nat) : List Nat :=
  (m23MaskPoints mask).sublists.filterMap
    (fun xs => if xs.length = 4 then some (m23Submask xs) else none)

@[expose]
public noncomputable def m23BlockFourSubmasks (i : Fin 253) : List Nat :=
  m23FourSubmasks (m23BlockMask i)

/-- Insert fresh masks into a compact bitset, failing at the first duplicate. -/
@[expose]
public def m23InsertFresh : List Nat → Nat → Option Nat
  | [], seen => some seen
  | x :: xs, seen =>
      if seen.testBit x then none
      else m23InsertFresh xs (seen ||| 2 ^ x)

/-- Check the first `n` blocks, in increasing index order, for repeated four-submasks. -/
@[expose]
public noncomputable def m23CheckBlocks : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, seen =>
      match m23InsertFresh
          (m23BlockFourSubmasks (Fin.ofNat 253 (253 - (n + 1)))) seen with
      | none => false
      | some seen' => m23CheckBlocks n seen'

private def m23Represents (seen : Nat) (prior : List Nat) : Prop :=
  ∀ x, seen.testBit x = true ↔ x ∈ prior

private theorem m23InsertFresh_sound
    {xs prior : List Nat} {seen seen' : Nat}
    (hseen : m23Represents seen prior)
    (hprior : prior.Nodup)
    (hrun : m23InsertFresh xs seen = some seen') :
    (prior ++ xs).Nodup ∧ m23Represents seen' (prior ++ xs) := by
  induction xs generalizing prior seen with
  | nil =>
      simp [m23InsertFresh] at hrun
      subst seen'
      simpa [m23Represents] using And.intro hprior hseen
  | cons x xs ih =>
      rw [m23InsertFresh] at hrun
      by_cases hx : seen.testBit x = true
      · simp [hx] at hrun
      · simp [hx] at hrun
        have hxmem : x ∉ prior := by
          intro hxp
          exact hx ((hseen x).2 hxp)
        have hpriorx : (prior ++ [x]).Nodup := by
          simpa [List.concat_eq_append] using hprior.concat hxmem
        have hseenx : m23Represents (seen ||| 2 ^ x) (prior ++ [x]) := by
          intro y
          rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true_iff,
            List.mem_append, List.mem_singleton]
          constructor
          · rintro (hy | hy)
            · exact Or.inl ((hseen y).1 hy)
            · exact Or.inr (of_decide_eq_true hy).symm
          · rintro (hy | hy)
            · exact Or.inl ((hseen y).2 hy)
            · exact Or.inr (by simp [hy])
        have hrest := ih hseenx hpriorx hrun
        have hlist : (prior ++ [x]) ++ xs = prior ++ x :: xs := by
          rw [List.append_assoc]
          rfl
        rw [hlist] at hrest
        exact hrest

private noncomputable def m23BlockFourSubmaskLists (n : Nat) : List (List Nat) :=
  List.ofFn (fun k : Fin n =>
    m23BlockFourSubmasks (Fin.ofNat 253 (253 - n + k.val)))

private theorem m23BlockFourSubmaskLists_succ {n : Nat} (hn : n + 1 ≤ 253) :
    m23BlockFourSubmaskLists (n + 1) =
      m23BlockFourSubmasks (Fin.ofNat 253 (253 - (n + 1))) ::
        m23BlockFourSubmaskLists n := by
  unfold m23BlockFourSubmaskLists
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  simp
  omega

private theorem m23CheckBlocks_sound
    {n seen : Nat} {prior : List Nat}
    (hn : n ≤ 253)
    (hseen : m23Represents seen prior)
    (hprior : prior.Nodup)
    (hcheck : m23CheckBlocks n seen = true) :
    (prior ++ (m23BlockFourSubmaskLists n).flatten).Nodup := by
  induction n generalizing seen prior with
  | zero =>
      simpa [m23BlockFourSubmaskLists] using hprior
  | succ n ih =>
      let current : Fin 253 := Fin.ofNat 253 (253 - (n + 1))
      change (match m23InsertFresh (m23BlockFourSubmasks current) seen with
        | none => false
        | some seen' => m23CheckBlocks n seen') = true at hcheck
      cases hrun : m23InsertFresh (m23BlockFourSubmasks current) seen with
      | none =>
          rw [hrun] at hcheck
          contradiction
      | some seen' =>
          rw [hrun] at hcheck
          have hins := m23InsertFresh_sound hseen hprior hrun
          have hrest := ih (by omega) hins.2 hins.1 hcheck
          rw [m23BlockFourSubmaskLists_succ hn]
          change (prior ++
            (m23BlockFourSubmasks current ++
              (m23BlockFourSubmaskLists n).flatten)).Nodup
          simpa only [List.append_assoc] using hrest

private theorem m23BlockFourSubmaskLists_full :
    m23BlockFourSubmaskLists 253 = List.ofFn m23BlockFourSubmasks := by
  unfold m23BlockFourSubmaskLists
  apply congrArg List.ofFn
  funext i
  congr 2
  apply Fin.ext
  simp

private theorem m23AllFourSubmasks_nodup_of_check
    (hcheck : m23CheckBlocks 253 0 = true) :
    (List.ofFn m23BlockFourSubmasks).flatten.Nodup := by
  have hseen : m23Represents 0 [] := by
    intro x
    simp
  have h := m23CheckBlocks_sound (n := 253) (prior := [])
    (by omega) hseen List.nodup_nil hcheck
  rw [m23BlockFourSubmaskLists_full] at h
  simpa using h

public theorem m23BlockFourSubmasks_disjoint_of_check
    (hcheck : m23CheckBlocks 253 0 = true)
    (i j : Fin 253) (hij : i ≠ j) :
    (m23BlockFourSubmasks i).Disjoint (m23BlockFourSubmasks j) := by
  have hpairs :
      List.Pairwise List.Disjoint (List.ofFn m23BlockFourSubmasks) :=
    (List.nodup_flatten.mp (m23AllFourSubmasks_nodup_of_check hcheck)).2
  have hindexed := List.pairwise_ofFn.mp hpairs
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hindexed hij
  · exact (hindexed hji).symm

private theorem m23MaskPoints_and (a b : Nat) :
    m23MaskPoints (a &&& b) = (m23MaskPoints a).filter b.testBit := by
  rw [m23MaskPoints, m23MaskPoints, List.filter_filter]
  apply List.filter_congr
  intro x hx
  rw [Nat.testBit_and]
  exact Bool.and_comm _ _

private theorem m23CommonCount_eq_maskPoints_length (i j : Fin 253) :
    m23CommonCount i j =
      (m23MaskPoints (m23BlockMask i &&& m23BlockMask j)).length := by
  rw [m23CommonCount, List.countP_eq_length_filter]
  rfl

private theorem m23Submask_mem_fourSubmasks
    {mask : Nat} {xs : List Nat}
    (hsub : xs.Sublist (m23MaskPoints mask))
    (hlen : xs.length = 4) :
    m23Submask xs ∈ m23FourSubmasks mask := by
  rw [m23FourSubmasks, List.mem_filterMap]
  exact ⟨xs, List.mem_sublists.mpr hsub, by simp [hlen]⟩

public theorem m23CommonCount_lt_four_of_check
    (hcheck : m23CheckBlocks 253 0 = true)
    (i j : Fin 253) (hij : i ≠ j) :
    m23CommonCount i j < 4 := by
  by_contra hnot
  have hfour : 4 ≤ m23CommonCount i j := by omega
  let common :=
    m23MaskPoints (m23BlockMask i &&& m23BlockMask j)
  let chosen := common.take 4
  have hcommon : 4 ≤ common.length := by
    rw [← m23CommonCount_eq_maskPoints_length i j]
    exact hfour
  have hlen : chosen.length = 4 :=
    List.length_take_of_le hcommon
  have hsubi : chosen.Sublist (m23MaskPoints (m23BlockMask i)) := by
    apply List.Sublist.trans (List.take_sublist 4 common)
    dsimp [common]
    rw [m23MaskPoints_and]
    exact List.filter_sublist
  have hsubj : chosen.Sublist (m23MaskPoints (m23BlockMask j)) := by
    apply List.Sublist.trans (List.take_sublist 4 common)
    dsimp [common]
    rw [Nat.and_comm, m23MaskPoints_and]
    exact List.filter_sublist
  have hmi : m23Submask chosen ∈ m23BlockFourSubmasks i :=
    m23Submask_mem_fourSubmasks hsubi hlen
  have hmj : m23Submask chosen ∈ m23BlockFourSubmasks j :=
    m23Submask_mem_fourSubmasks hsubj hlen
  exact (List.disjoint_iff_ne.mp
    (m23BlockFourSubmasks_disjoint_of_check hcheck i j hij)
    _ hmi _ hmj) rfl

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
set_option exponentiation.threshold 9000000

/-- The 8855 four-point submasks of the 253 listed blocks are all distinct. -/
public theorem m23FourSubmasks_unique_check : m23CheckBlocks 253 0 = true := by
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Indices of the W24 octads through point 24 whose deletions are the W23 heptads. -/
@[expose] public def m23BlockM24IndexArray : Array (Fin 759) := #[
  0, 11, 12, 15, 20, 27, 29, 30, 34, 37, 44, 47, 48, 54, 55, 62, 63, 65, 68, 71, 76, 81, 88, 89, 92, 95, 97, 98, 102, 108, 113, 115, 116, 126, 128, 129, 130, 134, 137, 139, 144, 147, 151, 154, 158, 165, 167, 171, 172, 178, 181, 185, 188, 189, 190, 196, 198, 203, 205, 206, 210, 211, 213, 219, 220, 223, 230, 231, 234, 237, 238, 241, 245, 246, 248, 249, 250, 257, 262, 266, 267, 270, 273, 275, 280, 283, 287, 290, 296, 301, 303, 307, 308, 311, 314, 315, 318, 322, 329, 331, 338, 342, 344, 345, 346, 355, 356, 360, 361, 365, 368, 370, 376, 381, 382, 383, 385, 386, 391, 393, 397, 398, 402, 405, 406, 415, 416, 418, 419, 420, 423, 427, 428, 429, 432, 439, 440, 446, 447, 453, 454, 456, 459, 463, 468, 470, 473, 483, 486, 489, 492, 493, 494, 497, 500, 507, 509, 510, 514, 515, 520, 521, 523, 527, 528, 530, 532, 533, 534, 541, 542, 545, 546, 551, 552, 561, 568, 569, 570, 573, 576, 577, 582, 585, 590, 591, 593, 594, 598, 602, 604, 605, 606, 609, 611, 615, 616, 619, 620, 627, 628, 632, 633, 635, 638, 641, 646, 647, 648, 651, 652, 654, 660, 664, 666, 671, 672, 675, 676, 677, 678, 682, 683, 689, 691, 695, 701, 702, 703, 706, 707, 712, 713, 716, 721, 723, 724, 725, 728, 732, 733, 734, 738, 739, 741, 742, 743, 746, 751, 754, 755, 756, 757
]

public theorem m23BlockM24IndexArray_size :
    m23BlockM24IndexArray.size = 253 := by decide +kernel

@[expose] public def m23BlockM24Index (i : Fin 253) : Fin 759 :=
  m23BlockM24IndexArray[i.val]'(by
    rw [m23BlockM24IndexArray_size]
    exact i.isLt)

private theorem m23BlockM24IndexRank_succ :
    ∀ i : Fin 252,
      759 - (m23BlockM24Index i.succ).val <
        759 - (m23BlockM24Index i.castSucc).val := by
  decide +kernel

private theorem m23BlockM24IndexRank_strictAnti :
    StrictAnti (fun i : Fin 253 => 759 - (m23BlockM24Index i).val) :=
  Fin.strictAnti_iff_succ_lt.mpr m23BlockM24IndexRank_succ

public theorem m23BlockM24Index_injective :
    Function.Injective m23BlockM24Index := by
  intro i j hij
  exact m23BlockM24IndexRank_strictAnti.injective
    (congrArg (fun x : Fin 759 => 759 - x.val) hij)

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row0 :
    m23AugmentedBlock (m23BlockAt (0 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (0 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row1 :
    m23AugmentedBlock (m23BlockAt (1 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (1 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row2 :
    m23AugmentedBlock (m23BlockAt (2 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (2 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row3 :
    m23AugmentedBlock (m23BlockAt (3 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (3 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row4 :
    m23AugmentedBlock (m23BlockAt (4 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (4 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row5 :
    m23AugmentedBlock (m23BlockAt (5 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (5 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row6 :
    m23AugmentedBlock (m23BlockAt (6 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (6 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row7 :
    m23AugmentedBlock (m23BlockAt (7 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (7 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row8 :
    m23AugmentedBlock (m23BlockAt (8 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (8 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row9 :
    m23AugmentedBlock (m23BlockAt (9 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (9 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row10 :
    m23AugmentedBlock (m23BlockAt (10 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (10 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row11 :
    m23AugmentedBlock (m23BlockAt (11 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (11 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row12 :
    m23AugmentedBlock (m23BlockAt (12 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (12 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row13 :
    m23AugmentedBlock (m23BlockAt (13 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (13 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row14 :
    m23AugmentedBlock (m23BlockAt (14 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (14 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row15 :
    m23AugmentedBlock (m23BlockAt (15 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (15 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row16 :
    m23AugmentedBlock (m23BlockAt (16 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (16 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row17 :
    m23AugmentedBlock (m23BlockAt (17 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (17 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row18 :
    m23AugmentedBlock (m23BlockAt (18 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (18 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row19 :
    m23AugmentedBlock (m23BlockAt (19 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (19 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row20 :
    m23AugmentedBlock (m23BlockAt (20 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (20 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row21 :
    m23AugmentedBlock (m23BlockAt (21 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (21 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row22 :
    m23AugmentedBlock (m23BlockAt (22 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (22 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row23 :
    m23AugmentedBlock (m23BlockAt (23 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (23 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row24 :
    m23AugmentedBlock (m23BlockAt (24 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (24 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row25 :
    m23AugmentedBlock (m23BlockAt (25 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (25 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row26 :
    m23AugmentedBlock (m23BlockAt (26 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (26 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row27 :
    m23AugmentedBlock (m23BlockAt (27 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (27 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row28 :
    m23AugmentedBlock (m23BlockAt (28 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (28 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row29 :
    m23AugmentedBlock (m23BlockAt (29 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (29 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row30 :
    m23AugmentedBlock (m23BlockAt (30 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (30 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row31 :
    m23AugmentedBlock (m23BlockAt (31 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (31 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row32 :
    m23AugmentedBlock (m23BlockAt (32 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (32 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row33 :
    m23AugmentedBlock (m23BlockAt (33 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (33 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row34 :
    m23AugmentedBlock (m23BlockAt (34 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (34 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row35 :
    m23AugmentedBlock (m23BlockAt (35 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (35 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row36 :
    m23AugmentedBlock (m23BlockAt (36 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (36 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row37 :
    m23AugmentedBlock (m23BlockAt (37 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (37 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row38 :
    m23AugmentedBlock (m23BlockAt (38 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (38 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row39 :
    m23AugmentedBlock (m23BlockAt (39 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (39 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row40 :
    m23AugmentedBlock (m23BlockAt (40 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (40 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row41 :
    m23AugmentedBlock (m23BlockAt (41 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (41 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row42 :
    m23AugmentedBlock (m23BlockAt (42 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (42 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row43 :
    m23AugmentedBlock (m23BlockAt (43 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (43 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row44 :
    m23AugmentedBlock (m23BlockAt (44 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (44 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row45 :
    m23AugmentedBlock (m23BlockAt (45 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (45 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row46 :
    m23AugmentedBlock (m23BlockAt (46 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (46 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row47 :
    m23AugmentedBlock (m23BlockAt (47 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (47 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row48 :
    m23AugmentedBlock (m23BlockAt (48 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (48 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row49 :
    m23AugmentedBlock (m23BlockAt (49 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (49 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row50 :
    m23AugmentedBlock (m23BlockAt (50 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (50 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row51 :
    m23AugmentedBlock (m23BlockAt (51 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (51 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row52 :
    m23AugmentedBlock (m23BlockAt (52 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (52 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row53 :
    m23AugmentedBlock (m23BlockAt (53 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (53 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row54 :
    m23AugmentedBlock (m23BlockAt (54 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (54 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row55 :
    m23AugmentedBlock (m23BlockAt (55 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (55 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row56 :
    m23AugmentedBlock (m23BlockAt (56 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (56 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row57 :
    m23AugmentedBlock (m23BlockAt (57 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (57 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row58 :
    m23AugmentedBlock (m23BlockAt (58 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (58 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row59 :
    m23AugmentedBlock (m23BlockAt (59 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (59 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row60 :
    m23AugmentedBlock (m23BlockAt (60 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (60 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row61 :
    m23AugmentedBlock (m23BlockAt (61 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (61 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row62 :
    m23AugmentedBlock (m23BlockAt (62 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (62 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row63 :
    m23AugmentedBlock (m23BlockAt (63 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (63 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row64 :
    m23AugmentedBlock (m23BlockAt (64 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (64 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row65 :
    m23AugmentedBlock (m23BlockAt (65 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (65 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row66 :
    m23AugmentedBlock (m23BlockAt (66 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (66 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row67 :
    m23AugmentedBlock (m23BlockAt (67 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (67 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row68 :
    m23AugmentedBlock (m23BlockAt (68 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (68 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row69 :
    m23AugmentedBlock (m23BlockAt (69 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (69 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row70 :
    m23AugmentedBlock (m23BlockAt (70 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (70 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row71 :
    m23AugmentedBlock (m23BlockAt (71 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (71 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row72 :
    m23AugmentedBlock (m23BlockAt (72 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (72 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row73 :
    m23AugmentedBlock (m23BlockAt (73 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (73 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row74 :
    m23AugmentedBlock (m23BlockAt (74 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (74 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row75 :
    m23AugmentedBlock (m23BlockAt (75 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (75 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row76 :
    m23AugmentedBlock (m23BlockAt (76 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (76 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row77 :
    m23AugmentedBlock (m23BlockAt (77 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (77 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row78 :
    m23AugmentedBlock (m23BlockAt (78 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (78 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row79 :
    m23AugmentedBlock (m23BlockAt (79 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (79 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row80 :
    m23AugmentedBlock (m23BlockAt (80 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (80 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row81 :
    m23AugmentedBlock (m23BlockAt (81 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (81 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row82 :
    m23AugmentedBlock (m23BlockAt (82 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (82 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row83 :
    m23AugmentedBlock (m23BlockAt (83 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (83 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row84 :
    m23AugmentedBlock (m23BlockAt (84 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (84 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row85 :
    m23AugmentedBlock (m23BlockAt (85 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (85 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row86 :
    m23AugmentedBlock (m23BlockAt (86 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (86 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row87 :
    m23AugmentedBlock (m23BlockAt (87 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (87 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row88 :
    m23AugmentedBlock (m23BlockAt (88 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (88 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row89 :
    m23AugmentedBlock (m23BlockAt (89 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (89 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row90 :
    m23AugmentedBlock (m23BlockAt (90 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (90 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row91 :
    m23AugmentedBlock (m23BlockAt (91 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (91 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row92 :
    m23AugmentedBlock (m23BlockAt (92 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (92 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row93 :
    m23AugmentedBlock (m23BlockAt (93 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (93 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row94 :
    m23AugmentedBlock (m23BlockAt (94 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (94 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row95 :
    m23AugmentedBlock (m23BlockAt (95 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (95 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row96 :
    m23AugmentedBlock (m23BlockAt (96 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (96 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row97 :
    m23AugmentedBlock (m23BlockAt (97 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (97 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row98 :
    m23AugmentedBlock (m23BlockAt (98 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (98 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row99 :
    m23AugmentedBlock (m23BlockAt (99 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (99 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row100 :
    m23AugmentedBlock (m23BlockAt (100 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (100 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row101 :
    m23AugmentedBlock (m23BlockAt (101 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (101 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row102 :
    m23AugmentedBlock (m23BlockAt (102 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (102 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row103 :
    m23AugmentedBlock (m23BlockAt (103 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (103 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row104 :
    m23AugmentedBlock (m23BlockAt (104 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (104 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row105 :
    m23AugmentedBlock (m23BlockAt (105 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (105 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row106 :
    m23AugmentedBlock (m23BlockAt (106 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (106 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row107 :
    m23AugmentedBlock (m23BlockAt (107 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (107 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row108 :
    m23AugmentedBlock (m23BlockAt (108 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (108 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row109 :
    m23AugmentedBlock (m23BlockAt (109 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (109 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row110 :
    m23AugmentedBlock (m23BlockAt (110 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (110 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row111 :
    m23AugmentedBlock (m23BlockAt (111 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (111 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row112 :
    m23AugmentedBlock (m23BlockAt (112 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (112 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row113 :
    m23AugmentedBlock (m23BlockAt (113 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (113 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row114 :
    m23AugmentedBlock (m23BlockAt (114 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (114 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row115 :
    m23AugmentedBlock (m23BlockAt (115 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (115 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row116 :
    m23AugmentedBlock (m23BlockAt (116 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (116 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row117 :
    m23AugmentedBlock (m23BlockAt (117 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (117 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row118 :
    m23AugmentedBlock (m23BlockAt (118 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (118 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row119 :
    m23AugmentedBlock (m23BlockAt (119 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (119 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row120 :
    m23AugmentedBlock (m23BlockAt (120 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (120 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row121 :
    m23AugmentedBlock (m23BlockAt (121 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (121 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row122 :
    m23AugmentedBlock (m23BlockAt (122 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (122 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row123 :
    m23AugmentedBlock (m23BlockAt (123 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (123 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row124 :
    m23AugmentedBlock (m23BlockAt (124 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (124 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row125 :
    m23AugmentedBlock (m23BlockAt (125 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (125 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row126 :
    m23AugmentedBlock (m23BlockAt (126 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (126 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row127 :
    m23AugmentedBlock (m23BlockAt (127 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (127 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row128 :
    m23AugmentedBlock (m23BlockAt (128 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (128 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row129 :
    m23AugmentedBlock (m23BlockAt (129 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (129 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row130 :
    m23AugmentedBlock (m23BlockAt (130 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (130 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row131 :
    m23AugmentedBlock (m23BlockAt (131 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (131 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row132 :
    m23AugmentedBlock (m23BlockAt (132 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (132 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row133 :
    m23AugmentedBlock (m23BlockAt (133 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (133 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row134 :
    m23AugmentedBlock (m23BlockAt (134 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (134 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row135 :
    m23AugmentedBlock (m23BlockAt (135 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (135 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row136 :
    m23AugmentedBlock (m23BlockAt (136 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (136 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row137 :
    m23AugmentedBlock (m23BlockAt (137 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (137 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row138 :
    m23AugmentedBlock (m23BlockAt (138 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (138 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row139 :
    m23AugmentedBlock (m23BlockAt (139 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (139 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row140 :
    m23AugmentedBlock (m23BlockAt (140 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (140 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row141 :
    m23AugmentedBlock (m23BlockAt (141 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (141 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row142 :
    m23AugmentedBlock (m23BlockAt (142 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (142 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row143 :
    m23AugmentedBlock (m23BlockAt (143 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (143 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row144 :
    m23AugmentedBlock (m23BlockAt (144 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (144 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row145 :
    m23AugmentedBlock (m23BlockAt (145 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (145 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row146 :
    m23AugmentedBlock (m23BlockAt (146 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (146 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row147 :
    m23AugmentedBlock (m23BlockAt (147 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (147 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row148 :
    m23AugmentedBlock (m23BlockAt (148 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (148 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row149 :
    m23AugmentedBlock (m23BlockAt (149 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (149 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row150 :
    m23AugmentedBlock (m23BlockAt (150 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (150 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row151 :
    m23AugmentedBlock (m23BlockAt (151 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (151 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row152 :
    m23AugmentedBlock (m23BlockAt (152 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (152 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row153 :
    m23AugmentedBlock (m23BlockAt (153 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (153 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row154 :
    m23AugmentedBlock (m23BlockAt (154 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (154 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row155 :
    m23AugmentedBlock (m23BlockAt (155 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (155 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row156 :
    m23AugmentedBlock (m23BlockAt (156 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (156 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row157 :
    m23AugmentedBlock (m23BlockAt (157 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (157 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row158 :
    m23AugmentedBlock (m23BlockAt (158 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (158 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row159 :
    m23AugmentedBlock (m23BlockAt (159 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (159 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row160 :
    m23AugmentedBlock (m23BlockAt (160 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (160 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row161 :
    m23AugmentedBlock (m23BlockAt (161 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (161 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row162 :
    m23AugmentedBlock (m23BlockAt (162 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (162 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row163 :
    m23AugmentedBlock (m23BlockAt (163 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (163 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row164 :
    m23AugmentedBlock (m23BlockAt (164 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (164 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row165 :
    m23AugmentedBlock (m23BlockAt (165 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (165 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row166 :
    m23AugmentedBlock (m23BlockAt (166 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (166 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row167 :
    m23AugmentedBlock (m23BlockAt (167 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (167 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row168 :
    m23AugmentedBlock (m23BlockAt (168 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (168 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row169 :
    m23AugmentedBlock (m23BlockAt (169 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (169 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row170 :
    m23AugmentedBlock (m23BlockAt (170 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (170 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row171 :
    m23AugmentedBlock (m23BlockAt (171 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (171 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row172 :
    m23AugmentedBlock (m23BlockAt (172 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (172 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row173 :
    m23AugmentedBlock (m23BlockAt (173 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (173 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row174 :
    m23AugmentedBlock (m23BlockAt (174 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (174 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row175 :
    m23AugmentedBlock (m23BlockAt (175 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (175 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row176 :
    m23AugmentedBlock (m23BlockAt (176 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (176 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row177 :
    m23AugmentedBlock (m23BlockAt (177 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (177 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row178 :
    m23AugmentedBlock (m23BlockAt (178 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (178 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row179 :
    m23AugmentedBlock (m23BlockAt (179 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (179 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row180 :
    m23AugmentedBlock (m23BlockAt (180 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (180 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row181 :
    m23AugmentedBlock (m23BlockAt (181 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (181 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row182 :
    m23AugmentedBlock (m23BlockAt (182 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (182 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row183 :
    m23AugmentedBlock (m23BlockAt (183 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (183 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row184 :
    m23AugmentedBlock (m23BlockAt (184 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (184 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row185 :
    m23AugmentedBlock (m23BlockAt (185 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (185 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row186 :
    m23AugmentedBlock (m23BlockAt (186 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (186 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row187 :
    m23AugmentedBlock (m23BlockAt (187 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (187 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row188 :
    m23AugmentedBlock (m23BlockAt (188 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (188 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row189 :
    m23AugmentedBlock (m23BlockAt (189 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (189 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row190 :
    m23AugmentedBlock (m23BlockAt (190 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (190 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row191 :
    m23AugmentedBlock (m23BlockAt (191 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (191 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row192 :
    m23AugmentedBlock (m23BlockAt (192 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (192 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row193 :
    m23AugmentedBlock (m23BlockAt (193 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (193 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row194 :
    m23AugmentedBlock (m23BlockAt (194 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (194 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row195 :
    m23AugmentedBlock (m23BlockAt (195 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (195 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row196 :
    m23AugmentedBlock (m23BlockAt (196 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (196 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row197 :
    m23AugmentedBlock (m23BlockAt (197 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (197 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row198 :
    m23AugmentedBlock (m23BlockAt (198 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (198 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row199 :
    m23AugmentedBlock (m23BlockAt (199 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (199 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row200 :
    m23AugmentedBlock (m23BlockAt (200 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (200 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row201 :
    m23AugmentedBlock (m23BlockAt (201 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (201 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row202 :
    m23AugmentedBlock (m23BlockAt (202 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (202 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row203 :
    m23AugmentedBlock (m23BlockAt (203 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (203 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row204 :
    m23AugmentedBlock (m23BlockAt (204 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (204 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row205 :
    m23AugmentedBlock (m23BlockAt (205 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (205 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row206 :
    m23AugmentedBlock (m23BlockAt (206 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (206 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row207 :
    m23AugmentedBlock (m23BlockAt (207 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (207 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row208 :
    m23AugmentedBlock (m23BlockAt (208 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (208 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row209 :
    m23AugmentedBlock (m23BlockAt (209 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (209 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row210 :
    m23AugmentedBlock (m23BlockAt (210 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (210 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row211 :
    m23AugmentedBlock (m23BlockAt (211 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (211 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row212 :
    m23AugmentedBlock (m23BlockAt (212 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (212 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row213 :
    m23AugmentedBlock (m23BlockAt (213 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (213 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row214 :
    m23AugmentedBlock (m23BlockAt (214 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (214 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row215 :
    m23AugmentedBlock (m23BlockAt (215 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (215 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row216 :
    m23AugmentedBlock (m23BlockAt (216 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (216 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row217 :
    m23AugmentedBlock (m23BlockAt (217 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (217 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row218 :
    m23AugmentedBlock (m23BlockAt (218 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (218 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row219 :
    m23AugmentedBlock (m23BlockAt (219 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (219 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row220 :
    m23AugmentedBlock (m23BlockAt (220 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (220 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row221 :
    m23AugmentedBlock (m23BlockAt (221 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (221 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row222 :
    m23AugmentedBlock (m23BlockAt (222 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (222 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row223 :
    m23AugmentedBlock (m23BlockAt (223 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (223 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row224 :
    m23AugmentedBlock (m23BlockAt (224 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (224 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row225 :
    m23AugmentedBlock (m23BlockAt (225 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (225 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row226 :
    m23AugmentedBlock (m23BlockAt (226 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (226 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row227 :
    m23AugmentedBlock (m23BlockAt (227 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (227 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row228 :
    m23AugmentedBlock (m23BlockAt (228 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (228 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row229 :
    m23AugmentedBlock (m23BlockAt (229 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (229 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row230 :
    m23AugmentedBlock (m23BlockAt (230 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (230 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row231 :
    m23AugmentedBlock (m23BlockAt (231 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (231 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row232 :
    m23AugmentedBlock (m23BlockAt (232 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (232 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row233 :
    m23AugmentedBlock (m23BlockAt (233 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (233 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row234 :
    m23AugmentedBlock (m23BlockAt (234 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (234 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row235 :
    m23AugmentedBlock (m23BlockAt (235 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (235 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row236 :
    m23AugmentedBlock (m23BlockAt (236 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (236 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row237 :
    m23AugmentedBlock (m23BlockAt (237 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (237 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row238 :
    m23AugmentedBlock (m23BlockAt (238 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (238 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row239 :
    m23AugmentedBlock (m23BlockAt (239 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (239 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row240 :
    m23AugmentedBlock (m23BlockAt (240 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (240 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row241 :
    m23AugmentedBlock (m23BlockAt (241 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (241 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row242 :
    m23AugmentedBlock (m23BlockAt (242 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (242 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row243 :
    m23AugmentedBlock (m23BlockAt (243 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (243 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row244 :
    m23AugmentedBlock (m23BlockAt (244 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (244 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row245 :
    m23AugmentedBlock (m23BlockAt (245 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (245 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row246 :
    m23AugmentedBlock (m23BlockAt (246 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (246 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row247 :
    m23AugmentedBlock (m23BlockAt (247 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (247 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row248 :
    m23AugmentedBlock (m23BlockAt (248 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (248 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row249 :
    m23AugmentedBlock (m23BlockAt (249 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (249 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row250 :
    m23AugmentedBlock (m23BlockAt (250 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (250 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row251 :
    m23AugmentedBlock (m23BlockAt (251 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (251 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

public theorem m23AugmentedBlockAt_eq_m24BlockAt_row252 :
    m23AugmentedBlock (m23BlockAt (252 : Fin 253)) =
      m24BlockAt (m23BlockM24Index (252 : Fin 253)) := by
  rw [Sporadic.Mathieu.m23AugmentedBlock_eq_insert_map]
  simp
  decide +kernel

open scoped Pointwise

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m23AugmentedBlockAt_eq_m24BlockAt
    (i : Fin 253) :
    m23AugmentedBlock (m23BlockAt i) =
      m24BlockAt (m23BlockM24Index i) := by
  exact match h : i.val with
  | 0 => by
      have hi : i = 0 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row0
  | 1 => by
      have hi : i = 1 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row1
  | 2 => by
      have hi : i = 2 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row2
  | 3 => by
      have hi : i = 3 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row3
  | 4 => by
      have hi : i = 4 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row4
  | 5 => by
      have hi : i = 5 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row5
  | 6 => by
      have hi : i = 6 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row6
  | 7 => by
      have hi : i = 7 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row7
  | 8 => by
      have hi : i = 8 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row8
  | 9 => by
      have hi : i = 9 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row9
  | 10 => by
      have hi : i = 10 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row10
  | 11 => by
      have hi : i = 11 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row11
  | 12 => by
      have hi : i = 12 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row12
  | 13 => by
      have hi : i = 13 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row13
  | 14 => by
      have hi : i = 14 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row14
  | 15 => by
      have hi : i = 15 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row15
  | 16 => by
      have hi : i = 16 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row16
  | 17 => by
      have hi : i = 17 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row17
  | 18 => by
      have hi : i = 18 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row18
  | 19 => by
      have hi : i = 19 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row19
  | 20 => by
      have hi : i = 20 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row20
  | 21 => by
      have hi : i = 21 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row21
  | 22 => by
      have hi : i = 22 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row22
  | 23 => by
      have hi : i = 23 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row23
  | 24 => by
      have hi : i = 24 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row24
  | 25 => by
      have hi : i = 25 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row25
  | 26 => by
      have hi : i = 26 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row26
  | 27 => by
      have hi : i = 27 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row27
  | 28 => by
      have hi : i = 28 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row28
  | 29 => by
      have hi : i = 29 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row29
  | 30 => by
      have hi : i = 30 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row30
  | 31 => by
      have hi : i = 31 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row31
  | 32 => by
      have hi : i = 32 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row32
  | 33 => by
      have hi : i = 33 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row33
  | 34 => by
      have hi : i = 34 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row34
  | 35 => by
      have hi : i = 35 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row35
  | 36 => by
      have hi : i = 36 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row36
  | 37 => by
      have hi : i = 37 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row37
  | 38 => by
      have hi : i = 38 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row38
  | 39 => by
      have hi : i = 39 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row39
  | 40 => by
      have hi : i = 40 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row40
  | 41 => by
      have hi : i = 41 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row41
  | 42 => by
      have hi : i = 42 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row42
  | 43 => by
      have hi : i = 43 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row43
  | 44 => by
      have hi : i = 44 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row44
  | 45 => by
      have hi : i = 45 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row45
  | 46 => by
      have hi : i = 46 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row46
  | 47 => by
      have hi : i = 47 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row47
  | 48 => by
      have hi : i = 48 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row48
  | 49 => by
      have hi : i = 49 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row49
  | 50 => by
      have hi : i = 50 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row50
  | 51 => by
      have hi : i = 51 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row51
  | 52 => by
      have hi : i = 52 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row52
  | 53 => by
      have hi : i = 53 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row53
  | 54 => by
      have hi : i = 54 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row54
  | 55 => by
      have hi : i = 55 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row55
  | 56 => by
      have hi : i = 56 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row56
  | 57 => by
      have hi : i = 57 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row57
  | 58 => by
      have hi : i = 58 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row58
  | 59 => by
      have hi : i = 59 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row59
  | 60 => by
      have hi : i = 60 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row60
  | 61 => by
      have hi : i = 61 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row61
  | 62 => by
      have hi : i = 62 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row62
  | 63 => by
      have hi : i = 63 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row63
  | 64 => by
      have hi : i = 64 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row64
  | 65 => by
      have hi : i = 65 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row65
  | 66 => by
      have hi : i = 66 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row66
  | 67 => by
      have hi : i = 67 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row67
  | 68 => by
      have hi : i = 68 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row68
  | 69 => by
      have hi : i = 69 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row69
  | 70 => by
      have hi : i = 70 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row70
  | 71 => by
      have hi : i = 71 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row71
  | 72 => by
      have hi : i = 72 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row72
  | 73 => by
      have hi : i = 73 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row73
  | 74 => by
      have hi : i = 74 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row74
  | 75 => by
      have hi : i = 75 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row75
  | 76 => by
      have hi : i = 76 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row76
  | 77 => by
      have hi : i = 77 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row77
  | 78 => by
      have hi : i = 78 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row78
  | 79 => by
      have hi : i = 79 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row79
  | 80 => by
      have hi : i = 80 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row80
  | 81 => by
      have hi : i = 81 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row81
  | 82 => by
      have hi : i = 82 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row82
  | 83 => by
      have hi : i = 83 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row83
  | 84 => by
      have hi : i = 84 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row84
  | 85 => by
      have hi : i = 85 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row85
  | 86 => by
      have hi : i = 86 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row86
  | 87 => by
      have hi : i = 87 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row87
  | 88 => by
      have hi : i = 88 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row88
  | 89 => by
      have hi : i = 89 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row89
  | 90 => by
      have hi : i = 90 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row90
  | 91 => by
      have hi : i = 91 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row91
  | 92 => by
      have hi : i = 92 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row92
  | 93 => by
      have hi : i = 93 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row93
  | 94 => by
      have hi : i = 94 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row94
  | 95 => by
      have hi : i = 95 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row95
  | 96 => by
      have hi : i = 96 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row96
  | 97 => by
      have hi : i = 97 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row97
  | 98 => by
      have hi : i = 98 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row98
  | 99 => by
      have hi : i = 99 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row99
  | 100 => by
      have hi : i = 100 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row100
  | 101 => by
      have hi : i = 101 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row101
  | 102 => by
      have hi : i = 102 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row102
  | 103 => by
      have hi : i = 103 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row103
  | 104 => by
      have hi : i = 104 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row104
  | 105 => by
      have hi : i = 105 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row105
  | 106 => by
      have hi : i = 106 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row106
  | 107 => by
      have hi : i = 107 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row107
  | 108 => by
      have hi : i = 108 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row108
  | 109 => by
      have hi : i = 109 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row109
  | 110 => by
      have hi : i = 110 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row110
  | 111 => by
      have hi : i = 111 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row111
  | 112 => by
      have hi : i = 112 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row112
  | 113 => by
      have hi : i = 113 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row113
  | 114 => by
      have hi : i = 114 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row114
  | 115 => by
      have hi : i = 115 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row115
  | 116 => by
      have hi : i = 116 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row116
  | 117 => by
      have hi : i = 117 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row117
  | 118 => by
      have hi : i = 118 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row118
  | 119 => by
      have hi : i = 119 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row119
  | 120 => by
      have hi : i = 120 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row120
  | 121 => by
      have hi : i = 121 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row121
  | 122 => by
      have hi : i = 122 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row122
  | 123 => by
      have hi : i = 123 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row123
  | 124 => by
      have hi : i = 124 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row124
  | 125 => by
      have hi : i = 125 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row125
  | 126 => by
      have hi : i = 126 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row126
  | 127 => by
      have hi : i = 127 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row127
  | 128 => by
      have hi : i = 128 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row128
  | 129 => by
      have hi : i = 129 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row129
  | 130 => by
      have hi : i = 130 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row130
  | 131 => by
      have hi : i = 131 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row131
  | 132 => by
      have hi : i = 132 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row132
  | 133 => by
      have hi : i = 133 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row133
  | 134 => by
      have hi : i = 134 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row134
  | 135 => by
      have hi : i = 135 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row135
  | 136 => by
      have hi : i = 136 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row136
  | 137 => by
      have hi : i = 137 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row137
  | 138 => by
      have hi : i = 138 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row138
  | 139 => by
      have hi : i = 139 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row139
  | 140 => by
      have hi : i = 140 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row140
  | 141 => by
      have hi : i = 141 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row141
  | 142 => by
      have hi : i = 142 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row142
  | 143 => by
      have hi : i = 143 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row143
  | 144 => by
      have hi : i = 144 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row144
  | 145 => by
      have hi : i = 145 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row145
  | 146 => by
      have hi : i = 146 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row146
  | 147 => by
      have hi : i = 147 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row147
  | 148 => by
      have hi : i = 148 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row148
  | 149 => by
      have hi : i = 149 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row149
  | 150 => by
      have hi : i = 150 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row150
  | 151 => by
      have hi : i = 151 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row151
  | 152 => by
      have hi : i = 152 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row152
  | 153 => by
      have hi : i = 153 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row153
  | 154 => by
      have hi : i = 154 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row154
  | 155 => by
      have hi : i = 155 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row155
  | 156 => by
      have hi : i = 156 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row156
  | 157 => by
      have hi : i = 157 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row157
  | 158 => by
      have hi : i = 158 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row158
  | 159 => by
      have hi : i = 159 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row159
  | 160 => by
      have hi : i = 160 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row160
  | 161 => by
      have hi : i = 161 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row161
  | 162 => by
      have hi : i = 162 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row162
  | 163 => by
      have hi : i = 163 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row163
  | 164 => by
      have hi : i = 164 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row164
  | 165 => by
      have hi : i = 165 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row165
  | 166 => by
      have hi : i = 166 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row166
  | 167 => by
      have hi : i = 167 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row167
  | 168 => by
      have hi : i = 168 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row168
  | 169 => by
      have hi : i = 169 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row169
  | 170 => by
      have hi : i = 170 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row170
  | 171 => by
      have hi : i = 171 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row171
  | 172 => by
      have hi : i = 172 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row172
  | 173 => by
      have hi : i = 173 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row173
  | 174 => by
      have hi : i = 174 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row174
  | 175 => by
      have hi : i = 175 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row175
  | 176 => by
      have hi : i = 176 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row176
  | 177 => by
      have hi : i = 177 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row177
  | 178 => by
      have hi : i = 178 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row178
  | 179 => by
      have hi : i = 179 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row179
  | 180 => by
      have hi : i = 180 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row180
  | 181 => by
      have hi : i = 181 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row181
  | 182 => by
      have hi : i = 182 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row182
  | 183 => by
      have hi : i = 183 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row183
  | 184 => by
      have hi : i = 184 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row184
  | 185 => by
      have hi : i = 185 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row185
  | 186 => by
      have hi : i = 186 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row186
  | 187 => by
      have hi : i = 187 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row187
  | 188 => by
      have hi : i = 188 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row188
  | 189 => by
      have hi : i = 189 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row189
  | 190 => by
      have hi : i = 190 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row190
  | 191 => by
      have hi : i = 191 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row191
  | 192 => by
      have hi : i = 192 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row192
  | 193 => by
      have hi : i = 193 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row193
  | 194 => by
      have hi : i = 194 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row194
  | 195 => by
      have hi : i = 195 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row195
  | 196 => by
      have hi : i = 196 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row196
  | 197 => by
      have hi : i = 197 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row197
  | 198 => by
      have hi : i = 198 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row198
  | 199 => by
      have hi : i = 199 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row199
  | 200 => by
      have hi : i = 200 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row200
  | 201 => by
      have hi : i = 201 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row201
  | 202 => by
      have hi : i = 202 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row202
  | 203 => by
      have hi : i = 203 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row203
  | 204 => by
      have hi : i = 204 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row204
  | 205 => by
      have hi : i = 205 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row205
  | 206 => by
      have hi : i = 206 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row206
  | 207 => by
      have hi : i = 207 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row207
  | 208 => by
      have hi : i = 208 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row208
  | 209 => by
      have hi : i = 209 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row209
  | 210 => by
      have hi : i = 210 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row210
  | 211 => by
      have hi : i = 211 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row211
  | 212 => by
      have hi : i = 212 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row212
  | 213 => by
      have hi : i = 213 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row213
  | 214 => by
      have hi : i = 214 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row214
  | 215 => by
      have hi : i = 215 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row215
  | 216 => by
      have hi : i = 216 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row216
  | 217 => by
      have hi : i = 217 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row217
  | 218 => by
      have hi : i = 218 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row218
  | 219 => by
      have hi : i = 219 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row219
  | 220 => by
      have hi : i = 220 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row220
  | 221 => by
      have hi : i = 221 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row221
  | 222 => by
      have hi : i = 222 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row222
  | 223 => by
      have hi : i = 223 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row223
  | 224 => by
      have hi : i = 224 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row224
  | 225 => by
      have hi : i = 225 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row225
  | 226 => by
      have hi : i = 226 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row226
  | 227 => by
      have hi : i = 227 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row227
  | 228 => by
      have hi : i = 228 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row228
  | 229 => by
      have hi : i = 229 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row229
  | 230 => by
      have hi : i = 230 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row230
  | 231 => by
      have hi : i = 231 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row231
  | 232 => by
      have hi : i = 232 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row232
  | 233 => by
      have hi : i = 233 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row233
  | 234 => by
      have hi : i = 234 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row234
  | 235 => by
      have hi : i = 235 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row235
  | 236 => by
      have hi : i = 236 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row236
  | 237 => by
      have hi : i = 237 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row237
  | 238 => by
      have hi : i = 238 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row238
  | 239 => by
      have hi : i = 239 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row239
  | 240 => by
      have hi : i = 240 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row240
  | 241 => by
      have hi : i = 241 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row241
  | 242 => by
      have hi : i = 242 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row242
  | 243 => by
      have hi : i = 243 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row243
  | 244 => by
      have hi : i = 244 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row244
  | 245 => by
      have hi : i = 245 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row245
  | 246 => by
      have hi : i = 246 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row246
  | 247 => by
      have hi : i = 247 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row247
  | 248 => by
      have hi : i = 248 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row248
  | 249 => by
      have hi : i = 249 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row249
  | 250 => by
      have hi : i = 250 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row250
  | 251 => by
      have hi : i = 251 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row251
  | 252 => by
      have hi : i = 252 := Fin.ext h
      subst i
      exact m23AugmentedBlockAt_eq_m24BlockAt_row252
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => by omega


/-- Distinct listed W23 heptads meet in fewer than four points. -/
public theorem m23BlockAt_inter
    (i j : Fin 253) (hij : i ≠ j) :
    (m23BlockAt i ∩ m23BlockAt j).card < 4 := by
  rw [← m23CommonCount_eq_card]
  exact m23CommonCount_lt_four_of_check
    m23FourSubmasks_unique_check i j hij

public theorem m23BlockAt_injective : Function.Injective m23BlockAt := by
  intro i j hij
  by_contra hne
  have hlt := m23BlockAt_inter i j hne
  rw [hij, Finset.inter_self, m23BlockAt_card] at hlt
  omega

public theorem m23BlocksCardinalityCheck : m23Blocks.card = 253 := by
  rw [m23Blocks, Finset.card_image_of_injective _ m23BlockAt_injective]
  simp

/-- Reduce a block-action equality to equality of the 23 incidence bits. -/
public theorem m23Perm_smul_blockAt_of_bits
    (g : Equiv.Perm (Fin 23)) (i j : Fin 253)
    (h : ∀ x : Fin 23,
      (m23BlockMask i).testBit (g.symm x).val =
        (m23BlockMask j).testBit x.val) :
    g • m23BlockAt i = m23BlockAt j := by
  ext x
  have hs : x ∈ g • m23BlockAt i ↔ g.symm x ∈ m23BlockAt i := by
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨y, hy, hgy⟩
      have hyx : y = g.symm x := by
        rw [← hgy]
        simp
      rwa [← hyx]
    · intro hx
      exact ⟨g.symm x, hx, by simp⟩
  rw [hs]
  simpa [m23BlockAt, m23MaskBlock] using congrArg (· = true) (h x)

/-- A surjective reindexing of all listed blocks proves preservation of the block set. -/
public theorem m23Blocks_smul_of_reindex
    (g : Equiv.Perm (Fin 23)) (f : Fin 253 → Fin 253)
    (hf : Function.Surjective f)
    (hblock : ∀ i, g • m23BlockAt i = m23BlockAt (f i)) :
    g • m23Blocks = m23Blocks := by
  ext B
  constructor
  · intro hB
    rw [Finset.mem_smul_finset] at hB
    rcases hB with ⟨C, hC, rfl⟩
    rw [m23Blocks] at hC ⊢
    rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
    exact Finset.mem_image.mpr
      ⟨f i, Finset.mem_univ _, (hblock i).symm⟩
  · intro hB
    rw [m23Blocks] at hB
    rcases Finset.mem_image.mp hB with ⟨j, _, rfl⟩
    rcases hf j with ⟨i, rfl⟩
    rw [Finset.mem_smul_finset]
    refine ⟨m23BlockAt i, ?_, hblock i⟩
    rw [m23Blocks]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Sporadic.Mathieu
