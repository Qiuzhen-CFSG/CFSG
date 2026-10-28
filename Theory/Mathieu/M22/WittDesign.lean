module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Data.Nat.Count

open Theory.GroupTheory

namespace Sporadic.Mathieu

open scoped Pointwise

set_option maxRecDepth 100000


/-- The 77 hexads as compact 22-bit incidence masks. -/
@[expose]
public noncomputable def m22BlockMaskArray : Array Nat := #[
  1311758, 2130070, 540774, 131847, 79878, 24858, 2101291, 66250,
  690186, 264754, 136274, 1638419, 1188002, 99618, 3148098, 303171,
  790914, 19587, 2631170, 1102338, 2572290, 2141, 41516, 151692,
  2687244, 1052980, 83476, 925716, 327845, 2231332, 9668, 2363972,
  1278020, 1575556, 313604, 562181, 3170309, 525496, 3277336, 364568,
  393576, 1132584, 2147400, 1585224, 1081737, 2369672, 7944, 803337,
  205833, 2170992, 180273, 1327312, 557904, 199056, 12945, 2360593,
  1092624, 2643984, 39136, 1050209, 2114464, 534817, 725536, 291872,
  3964960, 2752705, 86337, 158272, 855104, 427648, 3216512, 647296,
  1385216, 1721600, 2273536, 2198017, 1447937,
]

public theorem m22BlockMaskArray_size : m22BlockMaskArray.size = 77 := by decide +kernel

@[expose]
public noncomputable def m22BlockMask (i : Fin 77) : Nat :=
  m22BlockMaskArray[i.val]'(by rw [m22BlockMaskArray_size]; exact i.isLt)

/-- Decode a 22-bit incidence mask into a point set. -/
@[expose]
public noncomputable def m22MaskBlock (mask : Nat) : Finset (Fin 22) :=
  Finset.univ.filter (fun x => mask.testBit x.val = true)

/-- Decode the mask with the given certificate index. -/
@[expose]
public noncomputable def m22BlockAt (i : Fin 77) : Finset (Fin 22) :=
  m22MaskBlock (m22BlockMask i)

public theorem m22BlockAt_card : ∀ i, (m22BlockAt i).card = 6 := by decide +kernel

/-- The explicit finite set of all 77 hexads. -/
@[expose]
public noncomputable def m22Blocks : Finset (Finset (Fin 22)) :=
  Finset.univ.image m22BlockAt

public theorem m22BlockAt_image : Finset.univ.image m22BlockAt = m22Blocks := by
  rfl
/-- Reduce a block-action equality to equality of the 22 incidence bits. -/
public theorem m22Perm_smul_blockAt_of_bits
    (g : Equiv.Perm (Fin 22)) (i j : Fin 77)
    (h : ∀ x : Fin 22,
      (m22BlockMask i).testBit (g.symm x).val =
        (m22BlockMask j).testBit x.val) :
    g • m22BlockAt i = m22BlockAt j := by
  ext x
  have hs : x ∈ g • m22BlockAt i ↔ g.symm x ∈ m22BlockAt i := by
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
  simpa [m22BlockAt, m22MaskBlock] using congrArg (· = true) (h x)
private theorem m22BlockCardCheck :
    ∀ B ∈ m22Blocks, B.card = 6 := by
  intro B hB
  rw [m22Blocks] at hB
  rcases Finset.mem_image.mp hB with ⟨i, _, rfl⟩
  exact m22BlockAt_card i

public theorem m22Block_card
    (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) : B.card = 6 :=
  m22BlockCardCheck B hB

/-- The concrete degree-22 hexad table has 77 blocks. -/
public theorem m22Blocks_cardinality : m22Blocks.card = 77 := by decide +kernel

open scoped Pointwise
set_option maxRecDepth 100000

public theorem m22_blocks_smul_of_index (g : Equiv.Perm (Fin 22)) (index : Fin 77 → Fin 77)
    (hindex : Finset.univ.image index = Finset.univ)
    (hblock : ∀ i, g • m22BlockAt i = m22BlockAt (index i)) :
    g • m22Blocks = m22Blocks := by
  rw [← m22BlockAt_image]
  change Finset.image (g • m22BlockAt) Finset.univ = _
  rw [show (g • m22BlockAt) = m22BlockAt ∘ index by
    funext i
    exact hblock i]
  have himage :
      Finset.image m22BlockAt (Finset.image index Finset.univ) =
        Finset.image (fun x => m22BlockAt (index x)) Finset.univ := by
    simpa [Function.comp_def] using
      (Finset.image_image (s := Finset.univ) (f := index) (g := m22BlockAt))
  have hcomp :
      (m22BlockAt ∘ index) = (fun x => m22BlockAt (index x)) := by
    rfl
  rw [hcomp, ← himage, hindex]

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- All three-point subsets of the 22-point set. -/
@[expose]
public def m22ThreeSets : Finset (Finset (Fin 22)) :=
  Finset.univ.powersetCard 3

/-- Indices of listed hexads containing a given point set. -/
@[expose]
public noncomputable def m22ContainingBlocks (T : Finset (Fin 22)) : Finset (Fin 77) :=
  Finset.univ.filter fun i => T ⊆ m22BlockAt i

/-- A bounded partition of the three-point sets used by the uniqueness certificate. -/
@[expose]
public def m22ThreeSetsChunk (r : Fin 8) : Finset (Finset (Fin 22)) :=
  m22ThreeSets.filter (fun T =>
    T.sum (fun x : Fin 22 => x.val) % 8 = r.val)

/-- A bit mask for a finite set of points. -/
@[expose]
public def m22FinsetMask (T : Finset (Fin 22)) : Nat :=
  T.fold (· ||| ·) 0 (fun x => 2 ^ x.val)

private theorem m22FinsetMask_testBit (T : Finset (Fin 22)) (x : Fin 22) :
    (m22FinsetMask T).testBit x.val = true ↔ x ∈ T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [m22FinsetMask]
  | @insert a s ha ih =>
      simp only [m22FinsetMask]
      rw [Finset.fold_insert, Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true_iff]
      change
        (decide (a.val = x.val) = true ∨
          (m22FinsetMask s).testBit x.val = true) ↔ x ∈ insert a s
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

private theorem m22FinsetMask_lt (T : Finset (Fin 22)) :
    m22FinsetMask T < 2 ^ 22 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [m22FinsetMask]
  | @insert a s ha ih =>
      rw [m22FinsetMask, Finset.fold_insert]
      apply Nat.or_lt_two_pow
      · exact Nat.pow_lt_pow_right (by decide +kernel) (by omega)
      · exact ih
      · exact ha

private theorem m22BlockMask_lt : ∀ i : Fin 77, m22BlockMask i < 2 ^ 22 := by
  decide +kernel

private theorem m22FinsetMask_and_block_iff
    (T : Finset (Fin 22)) (i : Fin 77) :
    m22FinsetMask T &&& m22BlockMask i = m22FinsetMask T ↔
      T ⊆ m22BlockAt i := by
  constructor
  · intro h x hx
    have htx : (m22FinsetMask T).testBit x.val = true :=
      m22FinsetMask_testBit T x |>.2 hx
    have hand := congrArg (fun n => n.testBit x.val) h
    have hblock : (m22BlockMask i).testBit x.val = true := by
      simpa [Nat.testBit_and, htx] using hand
    simpa [m22BlockAt, m22MaskBlock] using hblock
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 22
    · let x : Fin 22 := ⟨k, hk⟩
      have hxiff := m22FinsetMask_testBit T x
      have hblockiff :
          (m22BlockMask i).testBit k = true ↔ x ∈ m22BlockAt i := by
        simp [m22BlockAt, m22MaskBlock, x]
      by_cases htk : (m22FinsetMask T).testBit k = true
      · have hxin : x ∈ T := by
          apply hxiff.1
          simpa [x] using htk
        have hxb : x ∈ m22BlockAt i := h hxin
        have hbtk : (m22BlockMask i).testBit k = true :=
          hblockiff.2 hxb
        simp [Nat.testBit_and, htk, hbtk]
      · simp [Nat.testBit_and, htk]
    · have hTbit : (m22FinsetMask T).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (m22FinsetMask_lt T)
          (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
      have hBbit : (m22BlockMask i).testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (m22BlockMask_lt i)
          (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
      simp [Nat.testBit_and, hTbit, hBbit]

private noncomputable def m22FastContainingBlocks
    (T : Finset (Fin 22)) : Finset (Fin 77) :=
  Finset.univ.filter fun i =>
    m22FinsetMask T &&& m22BlockMask i = m22FinsetMask T

@[expose]
public noncomputable def m22FastCount (T : Finset (Fin 22)) : Nat :=
  Nat.count (fun k =>
    m22FinsetMask T &&& m22BlockMask (Fin.ofNat 77 k) =
      m22FinsetMask T) 77

private theorem m22FastContainingBlocks_card_eq_count
    (T : Finset (Fin 22)) :
    (m22FastContainingBlocks T).card = m22FastCount T := by
  rw [m22FastCount, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    have hi' :
        m22FinsetMask T &&& m22BlockMask i = m22FinsetMask T := by
      simpa only [m22FastContainingBlocks, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    have hfin : Fin.ofNat 77 i.val = i := by
      apply Fin.ext
      simp [Fin.ofNat, i.isLt]
    have hiNat : i.val ∈
        (Finset.range 77).filter (fun k =>
          m22FinsetMask T &&& m22BlockMask (Fin.ofNat 77 k) =
            m22FinsetMask T) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr i.isLt, by rw [hfin]; exact hi'⟩
    exact hiNat
  · intro a ha b hb h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    have hfin : Fin.ofNat 77 b = (⟨b, hb.1⟩ : Fin 77) := by
      apply Fin.ext
      simp [Fin.ofNat, hb.1]
    rw [m22FastContainingBlocks, Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [hfin] at hb
      exact hb.2

public theorem m22ContainingBlocks_card_eq_fastCount
    (T : Finset (Fin 22)) :
    (m22ContainingBlocks T).card = m22FastCount T := by
  calc
    (m22ContainingBlocks T).card = (m22FastContainingBlocks T).card := by
      congr 1
      apply Finset.ext
      intro i
      simp only [m22ContainingBlocks, m22FastContainingBlocks,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact (m22FinsetMask_and_block_iff T i).symm
    _ = m22FastCount T := m22FastContainingBlocks_card_eq_count T

@[expose]
public noncomputable def m22FastAll
    (s : Finset (Finset (Fin 22))) : Bool :=
  s.fold (· && ·) true (fun T => decide (m22FastCount T = 1))

@[expose]
public noncomputable def m22ThreeSetsChunkCheck (r : Fin 8) : Bool :=
  m22FastAll (m22ThreeSetsChunk r)

private theorem m22FastAll_sound
    {s : Finset (Finset (Fin 22))} (hcheck : m22FastAll s = true)
    {T : Finset (Fin 22)} (hT : T ∈ s) :
    m22FastCount T = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hT
  | @insert a s ha ih =>
      rw [m22FastAll, Finset.fold_insert] at hcheck
      have hparts :
          decide (m22FastCount a = 1) = true ∧
            (Finset.fold (· && ·) true
              (fun T => decide (m22FastCount T = 1)) s) = true := by
        simpa [Bool.and_eq_true] using hcheck
      have htail : m22FastAll s = true := by
        simpa [m22FastAll] using hparts.2
      simp only [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · exact of_decide_eq_true hparts.1
      · exact ih htail hT
      · exact ha

public theorem m22ThreeSetsChunkCheck_sound
    {r : Fin 8} (hcheck : m22ThreeSetsChunkCheck r = true)
    {T : Finset (Fin 22)} (hT : T ∈ m22ThreeSetsChunk r) :
    m22FastCount T = 1 := by
  exact m22FastAll_sound (s := m22ThreeSetsChunk r)
    (by simpa [m22ThreeSetsChunkCheck] using hcheck) hT

public theorem m22ContainingBlocks_card_eq_one_of_check
    (hcheck :
      m22ThreeSets.filter (fun T => (m22ContainingBlocks T).card = 1) =
        m22ThreeSets)
    {T : Finset (Fin 22)} (hTcard : T.card = 3) :
    (m22ContainingBlocks T).card = 1 := by
  have hT : T ∈ m22ThreeSets := by
    rw [m22ThreeSets, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ T, hTcard⟩
  have hfiltered :
      T ∈ m22ThreeSets.filter
        (fun U => (m22ContainingBlocks U).card = 1) := by
    rw [hcheck]
    exact hT
  exact (Finset.mem_filter.mp hfiltered).2

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-0 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part0 :
    (m22ThreeSetsChunk 0).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 0 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (0 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-1 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part1 :
    (m22ThreeSetsChunk 1).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 1 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (1 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-2 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part2 :
    (m22ThreeSetsChunk 2).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 2 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (2 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-3 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part3 :
    (m22ThreeSetsChunk 3).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 3 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (3 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-4 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part4 :
    (m22ThreeSetsChunk 4).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 4 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (4 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-5 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part5 :
    (m22ThreeSetsChunk 5).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 5 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (5 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-6 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part6 :
    (m22ThreeSetsChunk 6).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 6 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (6 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Residue-7 slice of the three-point uniqueness certificate. -/
public theorem m22ThreeSets_unique_check_part7 :
    (m22ThreeSetsChunk 7).filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSetsChunk 7 := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    have hfast := m22ThreeSetsChunkCheck_sound
      (r := (7 : Fin 8)) (by decide +kernel) hT
    have hcard : (m22ContainingBlocks T).card = 1 := by
      rw [m22ContainingBlocks_card_eq_fastCount]
      exact hfast
    exact Finset.mem_filter.mpr ⟨hT, hcard⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

/-- Every three-set of points lies in exactly one of the 77 listed hexads. -/
public theorem m22ThreeSets_unique_check :
    m22ThreeSets.filter (fun T => (m22ContainingBlocks T).card = 1) =
      m22ThreeSets := by
  apply Finset.ext
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).1
  · intro hT
    let r : Fin 8 :=
      ⟨T.sum (fun x : Fin 22 => x.val) % 8, Nat.mod_lt _ (by decide +kernel)⟩
    have hTr : T ∈ m22ThreeSetsChunk r := by
      simp only [m22ThreeSetsChunk, Finset.mem_filter]
      exact ⟨hT, rfl⟩
    have hTfiltered : T ∈ (m22ThreeSetsChunk r).filter
        (fun U => (m22ContainingBlocks U).card = 1) := by
      have hr :
          r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨
            r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 := by
        omega
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      · have hr' : r = 0 := Fin.ext hr
        have hTr0 : T ∈ m22ThreeSetsChunk 0 := by
          simpa only [hr'] using hTr
        have hTf0 : T ∈ (m22ThreeSetsChunk 0).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part0]
          exact hTr0
        simpa only [hr'] using hTf0
      · have hr' : r = 1 := Fin.ext hr
        have hTr1 : T ∈ m22ThreeSetsChunk 1 := by
          simpa only [hr'] using hTr
        have hTf1 : T ∈ (m22ThreeSetsChunk 1).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part1]
          exact hTr1
        simpa only [hr'] using hTf1
      · have hr' : r = 2 := Fin.ext hr
        have hTr2 : T ∈ m22ThreeSetsChunk 2 := by
          simpa only [hr'] using hTr
        have hTf2 : T ∈ (m22ThreeSetsChunk 2).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part2]
          exact hTr2
        simpa only [hr'] using hTf2
      · have hr' : r = 3 := Fin.ext hr
        have hTr3 : T ∈ m22ThreeSetsChunk 3 := by
          simpa only [hr'] using hTr
        have hTf3 : T ∈ (m22ThreeSetsChunk 3).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part3]
          exact hTr3
        simpa only [hr'] using hTf3
      · have hr' : r = 4 := Fin.ext hr
        have hTr4 : T ∈ m22ThreeSetsChunk 4 := by
          simpa only [hr'] using hTr
        have hTf4 : T ∈ (m22ThreeSetsChunk 4).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part4]
          exact hTr4
        simpa only [hr'] using hTf4
      · have hr' : r = 5 := Fin.ext hr
        have hTr5 : T ∈ m22ThreeSetsChunk 5 := by
          simpa only [hr'] using hTr
        have hTf5 : T ∈ (m22ThreeSetsChunk 5).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part5]
          exact hTr5
        simpa only [hr'] using hTf5
      · have hr' : r = 6 := Fin.ext hr
        have hTr6 : T ∈ m22ThreeSetsChunk 6 := by
          simpa only [hr'] using hTr
        have hTf6 : T ∈ (m22ThreeSetsChunk 6).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part6]
          exact hTr6
        simpa only [hr'] using hTf6
      · have hr' : r = 7 := Fin.ext hr
        have hTr7 : T ∈ m22ThreeSetsChunk 7 := by
          simpa only [hr'] using hTr
        have hTf7 : T ∈ (m22ThreeSetsChunk 7).filter
            (fun U => (m22ContainingBlocks U).card = 1) := by
          rw [m22ThreeSets_unique_check_part7]
          exact hTr7
        simpa only [hr'] using hTf7
    exact Finset.mem_filter.mpr
      ⟨hT, (Finset.mem_filter.mp hTfiltered).2⟩

open scoped Pointwise

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

private theorem m22IndexedBlocks_inter_card_lt_3
    (i j : Fin 77) (hij : i ≠ j) :
    (m22BlockAt i ∩ m22BlockAt j).card < 3 := by
  by_contra hnot
  have hthree : 3 ≤ (m22BlockAt i ∩ m22BlockAt j).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq hthree
  have hTi : i ∈ m22ContainingBlocks T := by
    rw [m22ContainingBlocks, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hTsub.trans Finset.inter_subset_left⟩
  have hTj : j ∈ m22ContainingBlocks T := by
    rw [m22ContainingBlocks, Finset.mem_filter]
    exact ⟨Finset.mem_univ j, hTsub.trans Finset.inter_subset_right⟩
  have hone :=
    m22ContainingBlocks_card_eq_one_of_check
      m22ThreeSets_unique_check hTcard
  have hle : (m22ContainingBlocks T).card ≤ 1 := by omega
  exact hij ((Finset.card_le_one.mp hle) i hTi j hTj)

public theorem m22DistinctBlocks_inter_card_lt_3
    (B₁ : Finset (Fin 22)) (hB₁ : B₁ ∈ m22Blocks)
    (B₂ : Finset (Fin 22)) (hB₂ : B₂ ∈ m22Blocks)
    (hne : B₁ ≠ B₂) : (B₁ ∩ B₂).card < 3 := by
  have hB₁' : B₁ ∈ Finset.univ.image m22BlockAt := by
    rw [m22BlockAt_image]
    exact hB₁
  have hB₂' : B₂ ∈ Finset.univ.image m22BlockAt := by
    rw [m22BlockAt_image]
    exact hB₂
  rcases Finset.mem_image.mp hB₁' with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hB₂' with ⟨j, _, rfl⟩
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hne rfl
  exact m22IndexedBlocks_inter_card_lt_3 i j hij

/-- The concrete Witt S(3,6,22) design preserved by M22. -/
@[expose]
public noncomputable def m22WittDesign : SteinerSystem (Fin 22) 3 6 :=
  SteinerSystem.ofPairwiseIntersection m22Blocks m22Block_card
    m22DistinctBlocks_inter_card_lt_3 (by
      rw [m22Blocks_cardinality]
      decide +kernel)

end Sporadic.Mathieu
