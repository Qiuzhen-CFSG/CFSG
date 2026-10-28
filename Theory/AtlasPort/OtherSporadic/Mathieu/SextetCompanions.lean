/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.UnorderedSextets

/-!
The five tetrads complementary to a fixed tetrad inside octads.
The Witt design property gives unique coverage outside the tetrad; disjointness
and cardinality show that adjoining the original tetrad gives six parts.

Source: `Atlas/Mathieu/SextetCompanions.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open Finset
open scoped BigOperators

noncomputable def tetradCompanions (T : FourSet) : Finset (Finset Omega) :=
  (octads.filter (fun O => T.val ⊆ O)).image (fun O => O \ T.val)

theorem companion_mem (T : FourSet) (U : Finset Omega) : U ∈ tetradCompanions T ↔
    ∃ O ∈ octads, T.val ⊆ O ∧ O \ T.val = U := by
  classical
  simp only [tetradCompanions,mem_image,mem_filter]
  aesop

theorem companion_card (T : FourSet) (U : Finset Omega) (hU : U ∈ tetradCompanions T) : U.card = 4 := by
  obtain ⟨O,hO,hTO,rfl⟩ := (companion_mem T U).mp hU
  rw [card_sdiff_of_subset hTO,octad_size O hO,T.prop]

theorem companion_disjoint (T : FourSet) (U : Finset Omega) (hU : U ∈ tetradCompanions T) :
    Disjoint T.val U := by
  obtain ⟨O,hO,hTO,rfl⟩ := (companion_mem T U).mp hU
  exact disjoint_sdiff_self_right

theorem companion_union_octad (T : FourSet) (U : Finset Omega) (hU : U ∈ tetradCompanions T) :
    T.val ∪ U ∈ octads := by
  obtain ⟨O,hO,hTO,rfl⟩ := (companion_mem T U).mp hU
  rwa [union_sdiff_of_subset hTO]

theorem companion_unique_at_point (T : FourSet) (U V : Finset Omega)
    (hU : U ∈ tetradCompanions T) (hV : V ∈ tetradCompanions T)
    (p : Omega) (hpU : p ∈ U) (hpV : p ∈ V) : U = V := by
  classical
  obtain ⟨O,hO,hTO,rfl⟩ := (companion_mem T U).mp hU
  obtain ⟨P,hP,hTP,rfl⟩ := (companion_mem T V).mp hV
  have hp := mem_sdiff.mp hpU
  have hcard : (insert p T.val).card = 5 := by rw [card_insert_of_notMem hp.2,T.prop]
  have he : O = P := octad_unique_on_five (insert p T.val) O P hcard hO hP
    (insert_subset hp.1 hTO) (insert_subset (mem_sdiff.mp hpV).1 hTP)
  rw [he]

theorem companion_covers (T : FourSet) (p : Omega) (hp : p ∉ T.val) :
    ∃ U ∈ tetradCompanions T, p ∈ U := by
  classical
  have hc : (insert p T.val).card = 5 := by rw [card_insert_of_notMem hp,T.prop]
  obtain ⟨O,hO,_⟩ := octad_steiner (insert p T.val) hc
  refine ⟨O \ T.val,(companion_mem T _).mpr ⟨O,hO.1,?_,rfl⟩,?_⟩
  · exact (subset_insert _ _).trans hO.2
  · exact mem_sdiff.mpr ⟨hO.2 (mem_insert_self _ _),hp⟩

noncomputable def sextetCompletionParts (T : FourSet) : Finset (Finset Omega) :=
  insert T.val (tetradCompanions T)

theorem completion_part_card (T : FourSet) (U : Finset Omega)
    (hU : U ∈ sextetCompletionParts T) : U.card = 4 := by
  classical
  rcases mem_insert.mp hU with rfl | hU
  · exact T.prop
  · exact companion_card T U hU

theorem completion_partition (T : FourSet) (p : Omega) :
    ∃! U : Finset Omega, U ∈ sextetCompletionParts T ∧ p ∈ U := by
  classical
  by_cases hp : p ∈ T.val
  · refine ⟨T.val,⟨mem_insert_self _ _,hp⟩,?_⟩
    intro U hU
    rcases mem_insert.mp hU.1 with h | h
    · exact h
    · exact False.elim (disjoint_left.mp (companion_disjoint T U h) hp hU.2)
  · obtain ⟨U,hU,hpU⟩ := companion_covers T p hp
    refine ⟨U,⟨mem_insert_of_mem hU,hpU⟩,?_⟩
    intro V hV
    rcases mem_insert.mp hV.1 with h | h
    · exact False.elim (hp (h ▸ hV.2))
    · exact companion_unique_at_point T V U h hU p hV.2 hpU

theorem completion_six_parts (T : FourSet) : (sextetCompletionParts T).card = 6 := by
  classical
  let S := sextetCompletionParts T
  have hu : S.biUnion id = (univ : Finset Omega) := by
    ext p
    simp only [mem_biUnion,id_eq,mem_univ,iff_true]
    obtain ⟨U,hU,_⟩ := completion_partition T p
    exact ⟨U,hU⟩
  have hd : (S : Set (Finset Omega)).PairwiseDisjoint id := by
    intro U hU V hV hne
    apply disjoint_left.mpr
    intro p hpU hpV
    exact hne ((completion_partition T p).unique ⟨hU,hpU⟩ ⟨hV,hpV⟩)
  have hc := card_biUnion hd
  rw [hu] at hc
  have hh : ∑ U ∈ S, U.card = S.card * 4 := by
    calc
      _ = ∑ _U ∈ S, 4 := sum_congr rfl (fun U hU => completion_part_card T U hU)
      _ = _ := by simp
  dsimp only [id_eq] at hc
  rw [hh] at hc
  norm_num [Omega,HexIndex] at hc
  change S.card = 6
  omega

theorem companion_count (T : FourSet) : (tetradCompanions T).card = 5 := by
  classical
  have hn : T.val ∉ tetradCompanions T := by
    intro h
    have hd := companion_disjoint T T.val h
    have he : T.val = ∅ := disjoint_self.mp hd
    have hc := T.prop
    rw [he,card_empty] at hc
    contradiction
  have hh := completion_six_parts T
  rw [sextetCompletionParts,card_insert_of_notMem hn] at hh
  omega

end Atlas.Codes
