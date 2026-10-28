module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.FixedMasks
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.BinarySpan

/-!
# The Figure 1 pair in the selected Figure 2 images

The second Figure 1 pair generator has permutation `starElement 5`. It swaps
MOG points zero and one, whereas every Figure 2 generator fixes both. A whole
image containing this marked pair therefore cannot equal the raw Figure 2 row.
The four closures below retain the additional generator explicitly.

The signs in Figure 1(c) change the lift but not this permutation or its kernel
action. The added fixedness condition reduces both primed fixed spaces to the
corresponding unprimed space, of order sixteen.
Source: Kleidman--Wilson (1988), Figures 1(b,c) and 2; Section 2.3, pp.492--493.
-/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
@[expose] public section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image Cardinality.KernelCount SylowCore

/-- The permutation part shared by the AAB and BBB marked pairs. -/
def pairPermutation : StarGroup := starElement 5

/-- The whole quotient image includes the marked pair's permutation. -/
def pairRowGenerator (r : Fin 4) (j : Fin 4) : StarGroup :=
  if h : j.val < 3 then rowGenerator r ⟨j.val,h⟩ else pairPermutation

def pairRowImage (r : Fin 4) : Subgroup StarGroup :=
  closure (Set.range (pairRowGenerator r))

theorem pairRowGenerator_mem (r : Fin 4) (j : Fin 4) :
    pairRowGenerator r j ∈ pairRowImage r := subset_closure (Set.mem_range_self j)

theorem rowImage_le_pairRowImage (r : Fin 4) : rowImage r ≤ pairRowImage r := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  have h := pairRowGenerator_mem r (j.castLE (by decide))
  change (if h : j.val < 3 then rowGenerator r ⟨j.val,h⟩ else pairPermutation) ∈
    pairRowImage r at h
  rw [dif_pos j.isLt] at h
  exact h

theorem pairPermutation_mem_pairRowImage (r : Fin 4) : pairPermutation ∈ pairRowImage r :=
  pairRowGenerator_mem r 3

theorem pairRowImage_eq_sup (r : Fin 4) :
    pairRowImage r = rowImage r ⊔ closure ({pairPermutation} : Set StarGroup) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    unfold pairRowGenerator
    split_ifs with hj
    · exact (le_sup_left : rowImage r ≤ rowImage r ⊔ closure {pairPermutation})
        (rowGenerator_mem r ⟨j.val,hj⟩)
    · exact (le_sup_right : closure {pairPermutation} ≤ rowImage r ⊔ closure {pairPermutation})
        (subset_closure (Set.mem_singleton _))
  · exact sup_le (rowImage_le_pairRowImage r)
      ((closure_le _).mpr (Set.singleton_subset_iff.mpr (pairPermutation_mem_pairRowImage r)))


private theorem pairRowGenerator_square : ∀ r j,
    pairRowGenerator r j * pairRowGenerator r j = 1 := by
  intro r j
  apply Subtype.ext
  revert r j
  decide +kernel

private theorem pairRowGenerator_commute : ∀ r i j,
    Commute (pairRowGenerator r i) (pairRowGenerator r j) := by
  intro r i j
  apply Subtype.ext
  revert r i j
  decide +kernel


instance pairRowImage_elementary (r : Fin 4) : IsElementaryAbelian 2 (pairRowImage r) := by
  let : IsMulCommutative (closure (Set.range (pairRowGenerator r))) :=
    isMulCommutative_closure (by
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
      exact pairRowGenerator_commute r i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨j,rfl⟩
  simpa only [pow_two] using pairRowGenerator_square r j

/-- The raw rows fix point zero, so cannot contain the marked pair. -/
theorem rowImage_fixes_zero (r : Fin 4) {g : StarGroup} (hg : g ∈ rowImage r) :
    g.val 0 = 0 := by
  have hz : ∀ r j, (rowGenerator r j).val 0 = 0 := by decide +kernel
  have hle : rowImage r ≤ (MulAction.stabilizer (Equiv.Perm (Fin 24)) (0 : Fin 24)).comap
      StarGroup.subtype := by
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change (rowGenerator r j).val 0 = 0
    exact hz r j
  exact hle hg

theorem pairPermutation_not_mem_rowImage (r : Fin 4) : pairPermutation ∉ rowImage r := by
  intro h
  have he := rowImage_fixes_zero r h
  have hn : pairPermutation.val 0 ≠ 0 := by decide +kernel
  exact hn he

/-- Rows 0/2 have the same fixed kernel after adjoining the pair, as do 1/3. -/
def unprimedRow (r : Fin 4) : Fin 4 := ⟨r.val % 2, by omega⟩

def pairActionRows : Fin 11 → ℕ :=
  ![1, 2, 4, 1874, 1865, 1912, 1819, 128, 1385, 1640, 857]

private theorem pairActionRows_eq : ∀ i,
    pairActionRows i = pairLabel (pairPermutation.val (basisPair i).1)
      (pairPermutation.val (basisPair i).2) := by decide +kernel

theorem pairPermutation_mask (m : ℕ) :
    starMask pairPermutation m = maskImage pairActionRows m := by
  unfold starMask
  congr 1
  exact (funext pairActionRows_eq).symm


/-- This certificate includes the actual Figure 1 action, including primed rows. -/
theorem pair_fixedTest (r : Fin 4) (m : Fin 2048) :
    (fixedTest r m ∧ maskImage pairActionRows m.val = m.val) ↔
      fixedTest (unprimedRow r) m := by
  fin_cases r
  · change (fixedTest 0 m ∧ maskImage pairActionRows m.val = m.val) ↔ fixedTest 0 m
    simp only [fixedTest0]
    constructor
    · rintro ⟨hm,hs⟩
      simp only [fixedList0, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hs <;> decide +kernel
    · intro hm
      simp only [fixedList0, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · change (fixedTest 1 m ∧ maskImage pairActionRows m.val = m.val) ↔ fixedTest 1 m
    simp only [fixedTest1]
    constructor
    · rintro ⟨hm,hs⟩
      simp only [fixedList1, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hs <;> decide +kernel
    · intro hm
      simp only [fixedList1, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · change (fixedTest 2 m ∧ maskImage pairActionRows m.val = m.val) ↔ fixedTest 0 m
    simp only [fixedTest2, fixedTest0]
    constructor
    · rintro ⟨hm,hs⟩
      simp only [fixedList2, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hs <;> decide +kernel
    · intro hm
      simp only [fixedList0, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · change (fixedTest 3 m ∧ maskImage pairActionRows m.val = m.val) ↔ fixedTest 1 m
    simp only [fixedTest3, fixedTest1]
    constructor
    · rintro ⟨hm,hs⟩
      simp only [fixedList3, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hs <;> decide +kernel
    · intro hm
      simp only [fixedList1, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end Janko4.LocalStructure.ElementaryEightGeometry
