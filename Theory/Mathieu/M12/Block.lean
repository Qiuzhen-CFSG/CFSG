module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.List
public import Batteries
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Data.Nat.Count
import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M12.Generators

open Theory.GroupTheory

namespace Sporadic.Mathieu

/-!
# The Mathieu group `M₁₂` as the automorphism group of the Witt design W12

This file follows GLS, Number 3, Part I, Chapter A, Table 5.3b
(printed page 263, PDF page 280), together with the cited Aschbacher/Atlas
construction.  The concrete `S(5, 6, 12)` block set is the 132-element orbit
of `{1,2,3,4,5,9}` under the ATLAS degree-12 standard generators from
`M12G1-p12aB0.g1` and `M12G1-p12aB0.g2`.

The group is defined as the full automorphism group of this verified design.
Order and simplicity are intentionally deferred to later phases.
-/

open scoped Pointwise

set_option maxRecDepth 100000


/-- The 132 hexads as compact 12-bit incidence masks. -/
@[expose]
public noncomputable def m12BlockMaskArray : Array Nat := #[
  574, 2142, 1182, 287, 1134, 430, 2095, 207,
  846, 2702, 3342, 1551, 246, 2358, 1079, 1366,
  599, 918, 2199, 3606, 359, 2662, 679, 3238,
  1830, 2502, 1734, 3143, 1415, 2823, 378, 187,
  3130, 730, 1115, 2458, 1818, 2587, 2282, 619,
  1706, 2858, 1323, 1482, 2379, 3658, 907, 3211,
  1650, 2163, 1458, 2738, 819, 467, 3282, 2898,
  1683, 3347, 994, 1251, 3426, 2467, 3619, 2755,
  1859, 3970, 125, 2236, 1340, 476, 1628, 669,
  2844, 3101, 748, 2412, 1197, 813, 3628, 3276,
  1357, 2637, 1932, 2445, 884, 3188, 437, 1716,
  2613, 2772, 1237, 2389, 3476, 1813, 1508, 2277,
  1637, 2980, 3365, 965, 3908, 3717, 1272, 2680,
  952, 2361, 1593, 2265, 857, 3416, 1433, 3736,
  489, 1896, 3177, 3496, 2729, 3016, 1737, 3849,
  2544, 753, 1393, 3249, 3888, 2000, 3665, 2961,
  3808, 2913, 1953, 3521,
]

public theorem m12BlockMaskArray_size : m12BlockMaskArray.size = 132 := by decide +kernel

@[expose]
public noncomputable def m12BlockMask (i : Fin 132) : Nat :=
  m12BlockMaskArray[i.val]'(by rw [m12BlockMaskArray_size]; exact i.isLt)

/-- Decode a 12-bit incidence mask into a point set. -/
@[expose]
public noncomputable def m12MaskBlock (mask : Nat) : Finset (Fin 12) :=
  Finset.univ.filter (fun x => mask.testBit x.val = true)

/-- Decode the mask with the given certificate index. -/
@[expose]
public noncomputable def m12BlockAt (i : Fin 132) : Finset (Fin 12) :=
  m12MaskBlock (m12BlockMask i)

public theorem m12BlockAt_card : ∀ i, (m12BlockAt i).card = 6 := by decide +kernel

/-- The explicit finite set of all 132 hexads. -/
@[expose]
public noncomputable def m12Blocks : Finset (Finset (Fin 12)) :=
  Finset.univ.image m12BlockAt

public theorem m12BlockAt_image : Finset.univ.image m12BlockAt = m12Blocks := by
  rfl
/-- Reduce a block-action equality to equality of the 12 incidence bits. -/
public theorem m12Perm_smul_blockAt_of_bits
    (g : Equiv.Perm (Fin 12)) (i j : Fin 132)
    (h : ∀ x : Fin 12,
      (m12BlockMask i).testBit (g.symm x).val =
        (m12BlockMask j).testBit x.val) :
    g • m12BlockAt i = m12BlockAt j := by
  ext x
  have hs : x ∈ g • m12BlockAt i ↔ g.symm x ∈ m12BlockAt i := by
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
  simpa [m12BlockAt, m12MaskBlock] using congrArg (· = true) (h x)
private theorem m12BlockCardCheck :
    ∀ B ∈ m12Blocks, B.card = 6 := by
  intro B hB
  rw [m12Blocks] at hB
  rcases Finset.mem_image.mp hB with ⟨i, _, rfl⟩
  exact m12BlockAt_card i

public theorem m12Block_card
    (B : Finset (Fin 12)) (hB : B ∈ m12Blocks) : B.card = 6 :=
  m12BlockCardCheck B hB

/-- The concrete degree-12 hexad table has 132 blocks. -/
public theorem m12Blocks_cardinality : m12Blocks.card = 132 := by decide +kernel

open scoped Pointwise
set_option maxRecDepth 100000
@[expose] public def m12AIndexArray : Array (Fin 132) := #[19, 14, 2, 15, 73, 92, 85, 90, 93, 87, 68, 70, 18, 13, 1, 3, 16, 17, 12, 0, 91, 88, 89, 67, 72, 86, 71, 66, 69, 84, 57, 54, 32, 56, 34, 50, 36, 48, 123, 126, 111, 124, 109, 110, 122, 106, 125, 102, 37, 49, 35, 51, 55, 53, 31, 52, 33, 30, 127, 107, 105, 120, 103, 121, 108, 104, 27, 23, 10, 28, 11, 26, 24, 4, 101, 98, 79, 100, 78, 76, 80, 96, 82, 94, 29, 6, 25, 9, 21, 22, 7, 20, 5, 8, 83, 95, 81, 97, 75, 99, 77, 74, 47, 62, 65, 60, 45, 59, 64, 42, 43, 40, 131, 119, 114, 115, 128, 130, 118, 113, 61, 63, 44, 38, 41, 46, 39, 58, 116, 129, 117, 112]
public theorem m12AIndexArray_size : m12AIndexArray.size = 132 := by decide +kernel
public def m12AIndex (i : Fin 132) : Fin 132 :=
  m12AIndexArray[i.val]'(by
    rw [m12AIndexArray_size]
    exact i.isLt)

private theorem m12ABlock_bits (i : Fin 132) (x : Fin 12) :
    (m12BlockMask i).testBit (m12GeneratorA.symm x).val =
      (m12BlockMask (m12AIndex i)).testBit x.val := by
  revert i x
  decide +kernel

public theorem m12ABlockAt_smul (i : Fin 132) :
    m12GeneratorA • m12BlockAt i = m12BlockAt (m12AIndex i) :=
  m12Perm_smul_blockAt_of_bits _ _ _ (m12ABlock_bits i)

public theorem m12AIndex_image : Finset.univ.image m12AIndex = Finset.univ := by
  decide +kernel

open scoped Pointwise
set_option maxRecDepth 100000
@[expose] public def m12BIndexArray : Array (Fin 132) := #[3, 68, 69, 72, 110, 108, 105, 109, 36, 30, 104, 35, 80, 77, 83, 82, 10, 8, 75, 5, 119, 42, 44, 112, 46, 113, 43, 115, 117, 41, 93, 91, 86, 15, 92, 84, 17, 13, 122, 57, 53, 52, 127, 125, 124, 50, 55, 120, 28, 98, 99, 20, 29, 100, 94, 24, 25, 97, 64, 131, 130, 129, 61, 60, 65, 58, 73, 66, 71, 70, 2, 1, 0, 67, 34, 106, 107, 37, 31, 102, 111, 32, 33, 103, 11, 76, 81, 7, 6, 4, 79, 78, 74, 9, 118, 114, 47, 39, 116, 45, 40, 38, 90, 14, 16, 88, 18, 85, 19, 87, 89, 12, 126, 56, 123, 121, 49, 48, 54, 51, 96, 27, 101, 95, 22, 26, 23, 21, 59, 62, 63, 128]
public theorem m12BIndexArray_size : m12BIndexArray.size = 132 := by decide +kernel
public def m12BIndex (i : Fin 132) : Fin 132 :=
  m12BIndexArray[i.val]'(by
    rw [m12BIndexArray_size]
    exact i.isLt)

private theorem m12BBlock_bits (i : Fin 132) (x : Fin 12) :
    (m12BlockMask i).testBit (m12GeneratorB.symm x).val =
      (m12BlockMask (m12BIndex i)).testBit x.val := by
  revert i x
  decide +kernel

public theorem m12BBlockAt_smul (i : Fin 132) :
    m12GeneratorB • m12BlockAt i = m12BlockAt (m12BIndex i) :=
  m12Perm_smul_blockAt_of_bits _ _ _ (m12BBlock_bits i)

public theorem m12BIndex_image : Finset.univ.image m12BIndex = Finset.univ := by
  decide +kernel

open scoped Pointwise
set_option maxRecDepth 100000

public theorem m12_blocks_smul_of_index (g : Equiv.Perm (Fin 12)) (index : Fin 132 → Fin 132)
    (hindex : Finset.univ.image index = Finset.univ)
    (hblock : ∀ i, g • m12BlockAt i = m12BlockAt (index i)) :
    g • m12Blocks = m12Blocks := by
  rw [← m12BlockAt_image]
  change Finset.image (g • m12BlockAt) Finset.univ = _
  rw [show (g • m12BlockAt) = m12BlockAt ∘ index by
    funext i
    exact hblock i]
  have himage :
      Finset.image m12BlockAt (Finset.image index Finset.univ) =
        Finset.image (fun x => m12BlockAt (index x)) Finset.univ := by
    simpa [Function.comp_def] using
      (Finset.image_image (s := Finset.univ) (f := index) (g := m12BlockAt))
  have hcomp :
      (m12BlockAt ∘ index) = (fun x => m12BlockAt (index x)) := by
    rfl
  rw [hcomp, ← himage, hindex]

/-- The first ATLAS generator preserves the concrete hexad set. -/
public theorem m12GeneratorA_blocks_smul :
    m12GeneratorA • m12Blocks = m12Blocks := by
  exact m12_blocks_smul_of_index m12GeneratorA m12AIndex m12AIndex_image m12ABlockAt_smul

/-- The second ATLAS generator preserves the concrete hexad set. -/
public theorem m12GeneratorB_blocks_smul :
    m12GeneratorB • m12Blocks = m12Blocks := by
  exact m12_blocks_smul_of_index m12GeneratorB m12BIndex m12BIndex_image m12BBlockAt_smul

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- All five-point subsets of the 12-point set. -/
@[expose]
public def m12FiveSets : Finset (Finset (Fin 12)) :=
  Finset.univ.powersetCard 5

/-- Indices of listed hexads containing a given point set. -/
@[expose]
public noncomputable def m12ContainingBlocks (T : Finset (Fin 12)) : Finset (Fin 132) :=
  Finset.univ.filter fun i => T ⊆ m12BlockAt i

public theorem m12ContainingBlocks_card_eq_one_of_check
    (hcheck :
      m12FiveSets.filter (fun T => (m12ContainingBlocks T).card = 1) =
        m12FiveSets)
    {T : Finset (Fin 12)} (hTcard : T.card = 5) :
    (m12ContainingBlocks T).card = 1 := by
  have hT : T ∈ m12FiveSets := by
    rw [m12FiveSets, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ T, hTcard⟩
  have hfiltered :
      T ∈ m12FiveSets.filter
        (fun U => (m12ContainingBlocks U).card = 1) := by
    rw [hcheck]
    exact hT
  exact (Finset.mem_filter.mp hfiltered).2

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

@[expose] public def m12FinsetMask (T : Finset (Fin 12)) : Nat :=
  T.fold (· ||| ·) 0 (fun x => 2 ^ x.val)

private theorem m12FinsetMask_testBit (T : Finset (Fin 12)) (x : Fin 12) :
    (m12FinsetMask T).testBit x.val = true ↔ x ∈ T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [m12FinsetMask]
  | @insert a s ha ih =>
      simp only [m12FinsetMask]
      rw [Finset.fold_insert, Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true_iff]
      change
        (decide (a.val = x.val) = true ∨
          (m12FinsetMask s).testBit x.val = true) ↔ x ∈ insert a s
      simp only [Finset.mem_insert]
      rw [ih]
      simp only [decide_eq_true_eq]
      constructor <;> intro h
      · rcases h with h | h
        · left
          exact Fin.ext h.symm
        · exact Or.inr h
      · rcases h with h | h
        · left
          exact congrArg Fin.val h.symm
        · exact Or.inr h
      · exact ha

private theorem m12FinsetMask_lt (T : Finset (Fin 12)) :
    m12FinsetMask T < 2 ^ 12 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [m12FinsetMask]
  | @insert a s ha ih =>
      rw [m12FinsetMask, Finset.fold_insert]
      apply Nat.or_lt_two_pow
      · exact Nat.pow_lt_pow_right (by decide +kernel) (by omega)
      · exact ih
      · exact ha

private theorem m12BlockMask_lt : ∀ i : Fin 132, m12BlockMask i < 2 ^ 12 := by
  decide +kernel

private theorem m12FinsetMask_and_block_iff
    (T : Finset (Fin 12)) (i : Fin 132) :
    m12FinsetMask T &&& m12BlockMask i = m12FinsetMask T ↔
      T ⊆ m12BlockAt i := by
  constructor
  · intro h x hx
    have htx : (m12FinsetMask T).testBit x.val = true :=
      m12FinsetMask_testBit T x |>.2 hx
    have hand := congrArg (fun n => n.testBit x.val) h
    have hblock : (m12BlockMask i).testBit x.val = true := by
      simpa [Nat.testBit_and, htx] using hand
    simpa [m12BlockAt, m12MaskBlock] using hblock
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 12
    · let x : Fin 12 := ⟨k, hk⟩
      have hxiff := m12FinsetMask_testBit T x
      have hblockiff :
          (m12BlockMask i).testBit k = true ↔ x ∈ m12BlockAt i := by
        simp [m12BlockAt, m12MaskBlock, x]
      by_cases htk : (m12FinsetMask T).testBit k = true
      · have hxin : x ∈ T := by
          apply hxiff.1
          simpa [x] using htk
        have hxb : x ∈ m12BlockAt i := h hxin
        have hbtk : (m12BlockMask i).testBit k = true :=
          hblockiff.2 hxb
        simp [Nat.testBit_and, htk, hbtk]
      · simp [Nat.testBit_and, htk]
    · have hTbit : (m12FinsetMask T).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (m12FinsetMask_lt T)
          (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
      have hBbit : (m12BlockMask i).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (m12BlockMask_lt i)
          (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
      simp [Nat.testBit_and, hTbit, hBbit]

private noncomputable def m12FastContainingBlocks
    (T : Finset (Fin 12)) : Finset (Fin 132) :=
  Finset.univ.filter fun i =>
    m12FinsetMask T &&& m12BlockMask i = m12FinsetMask T

@[expose] public noncomputable def m12FastCount (T : Finset (Fin 12)) : Nat :=
  Nat.count (fun k =>
    m12FinsetMask T &&& m12BlockMask (Fin.ofNat 132 k) =
      m12FinsetMask T) 132

private theorem m12FastContainingBlocks_card_eq_count
    (T : Finset (Fin 12)) :
    (m12FastContainingBlocks T).card = m12FastCount T := by
  rw [m12FastCount, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    have hi' :
        m12FinsetMask T &&& m12BlockMask i = m12FinsetMask T := by
      simpa only [m12FastContainingBlocks, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    have hfin : Fin.ofNat 132 i.val = i := by
      apply Fin.ext
      simp [Fin.ofNat, i.isLt]
    have hiNat : i.val ∈
        (Finset.range 132).filter (fun k =>
          m12FinsetMask T &&& m12BlockMask (Fin.ofNat 132 k) =
            m12FinsetMask T) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr i.isLt, by rw [hfin]; exact hi'⟩
    exact hiNat
  · intro a ha b hb h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    have hfin : Fin.ofNat 132 b = (⟨b, hb.1⟩ : Fin 132) := by
      apply Fin.ext
      simp [Fin.ofNat, hb.1]
    rw [m12FastContainingBlocks, Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [hfin] at hb
      exact hb.2

public theorem m12ContainingBlocks_card_eq_fastCount
    (T : Finset (Fin 12)) :
    (m12ContainingBlocks T).card = m12FastCount T := by
  calc
    (m12ContainingBlocks T).card = (m12FastContainingBlocks T).card := by
      congr 1
      apply Finset.ext
      intro i
      simp only [m12ContainingBlocks, m12FastContainingBlocks,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact (m12FinsetMask_and_block_iff T i).symm
    _ = m12FastCount T := m12FastContainingBlocks_card_eq_count T

@[expose] public def m12FiveSetsChunk (k : Fin 8) : Finset (Finset (Fin 12)) :=
  m12FiveSets.filter (fun T => T.sum (fun x => (x : Nat)) % 8 = (k : Nat))

@[expose] public noncomputable def m12FastAll
    (s : Finset (Finset (Fin 12))) : Bool :=
  s.fold (· && ·) true (fun T => decide (m12FastCount T = 1))

@[expose] public noncomputable def m12FiveSetsChunkCheck (r : Fin 8) : Bool :=
  m12FastAll (m12FiveSetsChunk r)

private theorem m12FiveSetsChunkCheck_true (r : Fin 8) :
    m12FiveSetsChunkCheck r = true := by
  fin_cases r <;> decide +kernel

private theorem m12FastAll_sound
    {s : Finset (Finset (Fin 12))} (hcheck : m12FastAll s = true)
    {T : Finset (Fin 12)} (hT : T ∈ s) :
    m12FastCount T = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hT
  | @insert a s ha ih =>
      rw [m12FastAll, Finset.fold_insert] at hcheck
      have hparts :
          decide (m12FastCount a = 1) = true ∧
            (Finset.fold (· && ·) true
              (fun T => decide (m12FastCount T = 1)) s) = true := by
        simpa [Bool.and_eq_true] using hcheck
      have htail : m12FastAll s = true := by
        simpa [m12FastAll] using hparts.2
      simp only [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · exact of_decide_eq_true hparts.1
      · exact ih htail hT
      · exact ha

public theorem m12FiveSetsChunkCheck_sound
    {r : Fin 8} (hcheck : m12FiveSetsChunkCheck r = true)
    {T : Finset (Fin 12)} (hT : T ∈ m12FiveSetsChunk r) :
    m12FastCount T = 1 := by
  exact m12FastAll_sound (s := m12FiveSetsChunk r)
    (by simpa [m12FiveSetsChunkCheck] using hcheck) hT

/-- Every five-set of points lies in exactly one of the 132 listed hexads. -/
public theorem m12FiveSets_unique_check :
    m12FiveSets.filter (fun T => (m12ContainingBlocks T).card = 1) =
      m12FiveSets := by
  ext T
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hT
    let k : Fin 8 :=
      ⟨T.sum (fun x => (x : Nat)) % 8, Nat.mod_lt _ (by decide +kernel)⟩
    have hcheck : m12FiveSetsChunkCheck k = true :=
      m12FiveSetsChunkCheck_true k
    have hmem : T ∈ m12FiveSetsChunk k := by
      apply Finset.mem_filter.mpr
      exact ⟨hT, by simp [k]⟩
    have hfast : m12FastCount T = 1 :=
      m12FiveSetsChunkCheck_sound hcheck hmem
    exact ⟨hT, by rw [m12ContainingBlocks_card_eq_fastCount, hfast]⟩

open scoped Pointwise

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

private theorem m12IndexedBlocks_inter_card_lt_5
    (i j : Fin 132) (hij : i ≠ j) :
    (m12BlockAt i ∩ m12BlockAt j).card < 5 := by
  by_contra hnot
  have hfive : 5 ≤ (m12BlockAt i ∩ m12BlockAt j).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq hfive
  have hTi : i ∈ m12ContainingBlocks T := by
    rw [m12ContainingBlocks, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hTsub.trans Finset.inter_subset_left⟩
  have hTj : j ∈ m12ContainingBlocks T := by
    rw [m12ContainingBlocks, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, hTsub.trans Finset.inter_subset_right⟩
  have hone :=
    m12ContainingBlocks_card_eq_one_of_check
      m12FiveSets_unique_check hTcard
  have hle : (m12ContainingBlocks T).card ≤ 1 := by omega
  exact hij ((Finset.card_le_one.mp hle) i hTi j hTj)

public theorem m12DistinctBlocks_inter_card_lt_5
    (B₁ : Finset (Fin 12)) (hB₁ : B₁ ∈ m12Blocks)
    (B₂ : Finset (Fin 12)) (hB₂ : B₂ ∈ m12Blocks)
    (hne : B₁ ≠ B₂) : (B₁ ∩ B₂).card < 5 := by
  have hB₁' : B₁ ∈ Finset.univ.image m12BlockAt := by
    rw [m12BlockAt_image]
    exact hB₁
  have hB₂' : B₂ ∈ Finset.univ.image m12BlockAt := by
    rw [m12BlockAt_image]
    exact hB₂
  rcases Finset.mem_image.mp hB₁' with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hB₂' with ⟨j, _, rfl⟩
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hne rfl
  exact m12IndexedBlocks_inter_card_lt_5 i j hij

/-- The concrete Witt S(5,6,12) design. -/
@[expose]
public noncomputable def m12WittDesign : SteinerSystem (Fin 12) 5 6 :=
  SteinerSystem.ofPairwiseIntersection m12Blocks m12Block_card
    m12DistinctBlocks_inter_card_lt_5 (by
      rw [m12Blocks_cardinality]
      decide +kernel)

end Sporadic.Mathieu
