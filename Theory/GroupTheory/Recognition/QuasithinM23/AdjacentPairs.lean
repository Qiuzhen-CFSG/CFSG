module
public import Theory.GroupTheory.Recognition.QuasithinM23.TripleNormalizer
public import Theory.SpecificGroups.Alternating.SevenFiveSeed

/-!
# Adjacent pairs and a marked triple in A₇

An explicit even permutation fixes the distinguished pair and aligns the
third point of any marked triple. The same action identifies the intersection
of adjacent pair stabilizers as the pointwise triple fixer of order twelve.
This is the quotient calculation used by the M23 edge-fixer recognition.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.QuasithinM23
local notation "A7" => alternatingGroup (Fin 7)

private def swapPair (a : Fin 5) : A7 :=
  ![⟨Equiv.swap 0 6 * Equiv.swap 1 2, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 1 6 * Equiv.swap 0 2, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 2 6 * Equiv.swap 0 1, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 3 6 * Equiv.swap 0 1, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 4 6 * Equiv.swap 0 1, by change Equiv.Perm.sign _ = 1; decide⟩] a

private theorem swapPair_spec (a : Fin 5) :
    swapPair a ^ 2 = 1 ∧
    swapPair a • ({5,6} : Finset (Fin 7)) = {5,a.castLE (by decide)} ∧
    swapPair a • ({5,6,a.castLE (by decide)} : Finset (Fin 7)) =
      {5,6,a.castLE (by decide)} := by
  fin_cases a <;> decide +kernel

private theorem pair_intersection (a : Fin 5) :
    stabilizer A7 ({5,6} : Finset (Fin 7)) ⊓
      stabilizer A7 ({5,a.castLE (by decide)} : Finset (Fin 7)) =
    fixingSubgroup A7 (({5,6,a.castLE (by decide)} : Finset (Fin 7)) : Set (Fin 7)) := by
  classical
  let b : Fin 7 := a.castLE (by decide)
  have hi : ({5,6} : Finset (Fin 7)) ∩ {5,b} = {5} := by fin_cases a <;> decide
  have hd : ({5,6} : Finset (Fin 7)) \ {5,b} = {6} := by fin_cases a <;> decide
  have hd' : ({5,b} : Finset (Fin 7)) \ {5,6} = {b} := by fin_cases a <;> decide
  ext g
  constructor
  · rintro ⟨hx,hy⟩
    have hx : g • ({5,6} : Finset (Fin 7)) = {5,6} := hx
    have hy : g • ({5,b} : Finset (Fin 7)) = {5,b} := hy
    have h5 : g • (5 : Fin 7) = 5 := by
      have hh : g • (({5,6} : Finset (Fin 7)) ∩ {5,b}) = {5,6} ∩ {5,b} := by
        rw [Finset.smul_finset_inter,hx,hy]
      simpa only [hi,Finset.smul_finset_singleton,Finset.singleton_inj] using hh
    have h6 : g • (6 : Fin 7) = 6 := by
      have hh : g • (({5,6} : Finset (Fin 7)) \ {5,b}) = {5,6} \ {5,b} := by
        rw [Finset.smul_finset_sdiff,hx,hy]
      simpa only [hd,Finset.smul_finset_singleton,Finset.singleton_inj] using hh
    have hb : g • b = b := by
      have hh : g • (({5,b} : Finset (Fin 7)) \ {5,6}) = {5,b} \ {5,6} := by
        rw [Finset.smul_finset_sdiff,hy,hx]
      simpa only [hd',Finset.smul_finset_singleton,Finset.singleton_inj] using hh
    intro k
    have hk : k.val = 5 ∨ k.val = 6 ∨ k.val = b := by simpa using k.property
    rcases hk with hk | hk | hk <;> change g • k.val = k.val <;> rw [hk] <;> assumption
  · intro hg
    have h5 : g • (5 : Fin 7) = 5 := hg ⟨5,by simp⟩
    have h6 : g • (6 : Fin 7) = 6 := hg ⟨6,by simp⟩
    have hb : g • b = b := hg ⟨b,by simp [b]⟩
    constructor
    · change g • ({5,6} : Finset (Fin 7)) = {5,6}
      simp only [Finset.smul_finset_insert,Finset.smul_finset_singleton,h5,h6]
    · change g • ({5,b} : Finset (Fin 7)) = {5,b}
      simp only [Finset.smul_finset_insert,Finset.smul_finset_singleton,h5,hb]

private theorem pair_intersection_card (a : Fin 5) :
    Nat.card (stabilizer A7 ({5,6} : Finset (Fin 7)) ⊓
      stabilizer A7 ({5,a.castLE (by decide)} : Finset (Fin 7)) : Subgroup A7) = 12 := by
  classical
  rw [pair_intersection]
  let s : Finset (Fin 7) := {5,6,a.castLE (by decide)}
  have hc : Fintype.card ↥sᶜ = 4 := by fin_cases a <;> decide
  let e := (Atlas.Families.Alternating.stabilizerComplementEquiv s).trans
    (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq hc))
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  norm_num [Nat.factorial]

/-- A triple containing the original pair supplies an adjacent-pair reversal.
Its pointwise edge stabilizer has order twelve in the same A₇ action. -/
theorem seven_triple_pair_reversal (s : Finset (Fin 7)) (hs : s.card = 3)
    (h5 : (5 : Fin 7) ∈ s) (h6 : (6 : Fin 7) ∈ s) :
    ∃ t : A7, t ^ 2 = 1 ∧ t • s = s ∧
      t • ({5,6} : Finset (Fin 7)) ≠ {5,6} ∧
      Nat.card (stabilizer A7 ({5,6} : Finset (Fin 7)) ⊓
        stabilizer A7 (t • ({5,6} : Finset (Fin 7))) : Subgroup A7) = 12 := by
  classical
  obtain ⟨a,has,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({5,6} : Finset (Fin 7))) (t := s) (by rw [hs]; decide)
  have ha5 : a ≠ 5 := fun hh => ha (by simp [hh])
  have ha6 : a ≠ 6 := fun hh => ha (by simp [hh])
  have hal : a.val < 5 := by
    have h5' : a.val ≠ 5 := fun hh => ha5 (Fin.ext hh)
    have h6' : a.val ≠ 6 := fun hh => ha6 (Fin.ext hh)
    omega
  let b : Fin 5 := ⟨a.val,hal⟩
  have hb : b.castLE (by decide : 5 ≤ 7) = a := Fin.ext rfl
  have hs' : s = {5,6,a} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> assumption
    · rw [hs]
      simp [Ne.symm ha5,Ne.symm ha6]
  obtain ⟨ht2,hpair,htriple⟩ := swapPair_spec b
  rw [hb] at hpair htriple
  refine ⟨swapPair b,ht2,by simpa only [hs'] using htriple,?_,?_⟩
  · rw [hpair]
    intro hh
    have ha' : a ∈ ({5,6} : Finset (Fin 7)) := hh ▸ (by simp : a ∈ ({5,a} : Finset (Fin 7)))
    exact ha ha'
  · rw [hpair,←hb]
    exact pair_intersection_card b

private def alignThird (a : Fin 5) : A7 :=
  ![⟨Equiv.swap 0 4 * Equiv.swap 1 2, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 1 4 * Equiv.swap 0 2, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 2 4 * Equiv.swap 0 1, by change Equiv.Perm.sign _ = 1; decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 0 1, by change Equiv.Perm.sign _ = 1; decide⟩,
    1] a

private theorem alignThird_spec (a : Fin 5) :
    (alignThird a : Equiv.Perm (Fin 7)) 5 = 5 ∧
    (alignThird a : Equiv.Perm (Fin 7)) 6 = 6 ∧
    alignThird a • ({5,6,a.castLE (by decide)} : Finset (Fin 7)) = {4,5,6} := by
  fin_cases a <;> decide +kernel

/-- Align a triple by an even permutation fixing both original pair points. -/
theorem seven_pair_triple_alignment (s : Finset (Fin 7)) (hs : s.card = 3)
    (h5 : (5 : Fin 7) ∈ s) (h6 : (6 : Fin 7) ∈ s) :
    ∃ a : A7, (a : Equiv.Perm (Fin 7)) 5 = 5 ∧
      (a : Equiv.Perm (Fin 7)) 6 = 6 ∧ a • s = ({4,5,6} : Finset (Fin 7)) := by
  classical
  obtain ⟨a,has,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({5,6} : Finset (Fin 7))) (t := s) (by rw [hs]; decide)
  have ha5 : a ≠ 5 := fun hh => ha (by simp [hh])
  have ha6 : a ≠ 6 := fun hh => ha (by simp [hh])
  have hal : a.val < 5 := by
    have h5' : a.val ≠ 5 := fun hh => ha5 (Fin.ext hh)
    have h6' : a.val ≠ 6 := fun hh => ha6 (Fin.ext hh)
    omega
  let b : Fin 5 := ⟨a.val,hal⟩
  have hb : b.castLE (by decide : 5 ≤ 7) = a := Fin.ext rfl
  have hs' : s = {5,6,a} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> assumption
    · rw [hs]
      simp [Ne.symm ha5,Ne.symm ha6]
  obtain ⟨h5',h6',ht⟩ := alignThird_spec b
  exact ⟨alignThird b,h5',h6',by simpa only [hb,hs'] using ht⟩

/-- The pointwise fixer of the standard adjacent pair edge has order twelve. -/
theorem seven_adjacent_pair_stabilizer_card :
    Nat.card (stabilizer A7 ({5,6} : Finset (Fin 7)) ⊓
      stabilizer A7 ({4,5} : Finset (Fin 7)) : Subgroup A7) = 12 := by
  have hh := pair_intersection_card (4 : Fin 5)
  change Nat.card (stabilizer A7 ({5,6} : Finset (Fin 7)) ⊓
    stabilizer A7 ({5,4} : Finset (Fin 7)) : Subgroup A7) = 12 at hh
  rwa [Finset.pair_comm (5 : Fin 7) 4] at hh

end Theory.GroupTheory.QuasithinM23
