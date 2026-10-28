/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.WittDesign

/-!
The distinguished sextet, trio and Kleinian markings of the Golay coordinates.
Explicit tetrad and letter-pair embeddings prove the required partitions
and identify the unions which are octads.

Source: `Atlas/Codes/GolayMarkings.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset

def tetradEmbedding (i : HexIndex) : Fin 4 ↪ Omega := ⟨fun k => (i,k), fun _ _ h => (Prod.mk.inj h).2⟩
def tetrad (i : HexIndex) : Finset Omega := univ.map (tetradEmbedding i)

@[simp] theorem mem_tetrad (p : Omega) (i : HexIndex) : p ∈ tetrad i ↔ p.1 = i := by
  rw [tetrad, mem_map]
  constructor
  · rintro ⟨k,_,he⟩
    exact (congrArg Prod.fst he).symm
  · intro h
    exact ⟨p.2,mem_univ _,Prod.ext h.symm rfl⟩

theorem tetrad_card (i : HexIndex) : (tetrad i).card = 4 := by simp [tetrad]
theorem tetrads_partition (p : Omega) : ∃! i : HexIndex, p ∈ tetrad i := by
  simp only [mem_tetrad]
  exact ⟨p.1,rfl,fun _ h => h.symm⟩
theorem tetrads_disjoint (i j : HexIndex) (hij : i ≠ j) : Disjoint (tetrad i) (tetrad j) := by
  apply disjoint_left.mpr
  intro p hi hj
  exact hij ((mem_tetrad p i).mp hi ▸ (mem_tetrad p j).mp hj)

theorem tetrad_pair_octad (i j : HexIndex) (hij : i ≠ j) : tetrad i ∪ tetrad j ∈ octads := by
  let r : Fin 6 → Bit := Pi.single (hexIndexEquiv i) 1 + Pi.single (hexIndexEquiv j) 1
  have he : hexIndexEquiv i ≠ hexIndexEquiv j := fun h => hij (hexIndexEquiv.injective h)
  have hr : r ∈ P6 := (parityCode_mem 5 _).mpr (by simp [r, sum_add_distrib])
  have hw : rho r ∈ golay := C0_le_golay ⟨(0,⟨r,hr⟩),by simp [c0Encoder]⟩
  have hs : support (rho r) = tetrad i ∪ tetrad j := by
    ext p
    simp only [support, mem_filter, mem_univ, true_and, mem_union, mem_tetrad]
    change r (hexIndexEquiv p.1) ≠ 0 ↔ p.1 = i ∨ p.1 = j
    by_cases hi : p.1 = i
    · subst i; simp [r, he]
    by_cases hj : p.1 = j
    · subst j; simp [r, he.symm]
    · have hi' : hexIndexEquiv p.1 ≠ hexIndexEquiv i := fun h => hi (hexIndexEquiv.injective h)
      have hj' : hexIndexEquiv p.1 ≠ hexIndexEquiv j := fun h => hj (hexIndexEquiv.injective h)
      simp [r, hi, hj, hi', hj']
  have hn : hammingNorm (rho r) = 8 := by
    change (support (rho r)).card = 8
    rw [hs, card_union_of_disjoint (tetrads_disjoint i j hij), tetrad_card, tetrad_card]
  exact (octads_mem _).mpr ⟨⟨rho r,hw⟩,hn,hs⟩

structure IsSextet (T : HexIndex → Finset Omega) : Prop where
  tetrad_size : ∀ i, (T i).card = 4
  partition : ∀ p, ∃! i, p ∈ T i
  pair_octads : ∀ i j, i ≠ j → T i ∪ T j ∈ octads

theorem distinguished_sextet : IsSextet tetrad :=
  ⟨tetrad_card,tetrads_partition,tetrad_pair_octad⟩

def distinguishedTrio (i : Fin 3) : Finset Omega := tetrad (i,0) ∪ tetrad (i,1)

theorem distinguishedTrio_octads (i : Fin 3) : distinguishedTrio i ∈ octads :=
  tetrad_pair_octad (i,0) (i,1) (by simp)

theorem distinguishedTrio_compatibility (i : Fin 3) (p : Omega) :
    p ∈ distinguishedTrio i ↔ p.1.1 = i := by
  simp only [distinguishedTrio, mem_union, mem_tetrad]
  rcases p with ⟨⟨j,k⟩,l⟩
  fin_cases k <;> simp

theorem distinguishedTrio_partition (p : Omega) : ∃! i : Fin 3, p ∈ distinguishedTrio i := by
  simp only [distinguishedTrio_compatibility]
  exact ⟨p.1.1,rfl,fun _ h => h.symm⟩

def letterPair (u : K) (s : Fin 2) : Finset (Fin 4) :=
  univ.filter (fun k => if s = 0 then j u k = 1 else j u k = 0)

theorem letterPair_table :
    (letterPair a 0 = {2,3} ∧ letterPair a 1 = {0,1}) ∧
    (letterPair b 0 = {1,3} ∧ letterPair b 1 = {0,2}) ∧
    (letterPair c 0 = {1,2} ∧ letterPair c 1 = {0,3}) := by decide

theorem letterPair_card : ∀ u : K, u ≠ 0 → ∀ s, (letterPair u s).card = 2 := by decide

theorem letterPair_partition : ∀ (u : K) (k : Fin 4), ∃! s : Fin 2, k ∈ letterPair u s := by
  unfold ExistsUnique
  decide

abbrev KleinianMarking := {m : HexIndex → K // ∀ i, m i ≠ 0}
def distinguishedMarking : KleinianMarking := ⟨fun _ => a, by intro i; exact (by decide : a ≠ 0)⟩
def markedPair (m : KleinianMarking) (t : HexIndex × Fin 2) : Finset Omega :=
  (letterPair (m.val t.1) t.2).map (tetradEmbedding t.1)

theorem markedPair_card (m : KleinianMarking) (t : HexIndex × Fin 2) : (markedPair m t).card = 2 := by
  rw [markedPair, card_map]
  exact letterPair_card _ (m.prop t.1) t.2

theorem markedPair_mem (m : KleinianMarking) (t : HexIndex × Fin 2) (p : Omega) :
    p ∈ markedPair m t ↔ p.1 = t.1 ∧ p.2 ∈ letterPair (m.val t.1) t.2 := by
  simp only [markedPair, mem_map]
  constructor
  · rintro ⟨k,hk,h⟩
    have he : (t.1,k) = p := h
    cases he
    exact ⟨rfl,hk⟩
  · rintro ⟨h,hk⟩
    exact ⟨p.2,hk,Prod.ext h.symm rfl⟩

theorem markedPair_subset_tetrad (m : KleinianMarking) (t : HexIndex × Fin 2) :
    markedPair m t ⊆ tetrad t.1 := fun p hp => (mem_tetrad p t.1).mpr ((markedPair_mem m t p).mp hp).1

theorem markedPairs_partition (m : KleinianMarking) (p : Omega) :
    ∃! t : HexIndex × Fin 2, p ∈ markedPair m t := by
  obtain ⟨s,hs,hu⟩ := letterPair_partition (m.val p.1) p.2
  refine ⟨(p.1,s),(markedPair_mem m _ p).mpr ⟨rfl,hs⟩,?_⟩
  rintro ⟨i,t⟩ ht
  obtain ⟨hi,ht⟩ := (markedPair_mem m (i,t) p).mp ht
  dsimp at hi ht
  subst i
  exact Prod.ext rfl (hu t ht)

end Atlas.Codes
