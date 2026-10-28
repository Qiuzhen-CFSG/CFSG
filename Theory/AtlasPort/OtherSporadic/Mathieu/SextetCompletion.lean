/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCompanions

/-!
Every tetrad lies in a unique unordered sextet.
Addition of binary words shows that pairs of companion tetrads form octads;
these companions construct the completion and force its uniqueness.

Source: `Atlas/Mathieu/SextetCompletion.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open Finset

/-- Binary addition is symmetric difference of supports. -/
theorem support_add_sdiff (u v : BinaryWord) :
    support (u+v) = (support u \ support v) ∪ (support v \ support u) := by
  classical
  ext p
  simp only [support,mem_union,mem_sdiff,mem_filter,mem_univ,true_and,Pi.add_apply]
  have h : ∀ x y : Bit, x+y ≠ 0 ↔ (x ≠ 0 ∧ ¬y ≠ 0) ∨ (y ≠ 0 ∧ ¬x ≠ 0) := by decide
  exact h _ _

theorem octad_union_from_common_tetrad (T U V : Finset Omega)
    (hTU : Disjoint T U) (hTV : Disjoint T V) (hUV : Disjoint U V)
    (hU : U.card = 4) (hV : V.card = 4)
    (hoU : T ∪ U ∈ octads) (hoV : T ∪ V ∈ octads) : U ∪ V ∈ octads := by
  classical
  obtain ⟨u,hu,hsu⟩ := (octads_mem _).mp hoU
  obtain ⟨v,hv,hsv⟩ := (octads_mem _).mp hoV
  have hs : support (u.val+v.val) = U ∪ V := by
    rw [support_add_sdiff,hsu,hsv]
    ext p
    have htu : p ∈ T → p ∈ U → False := fun h h' => disjoint_left.mp hTU h h'
    have htv : p ∈ T → p ∈ V → False := fun h h' => disjoint_left.mp hTV h h'
    have huv : p ∈ U → p ∈ V → False := fun h h' => disjoint_left.mp hUV h h'
    simp only [mem_union,mem_sdiff]
    tauto
  refine (octads_mem _).mpr ⟨⟨u.val+v.val,golay.add_mem u.prop v.prop⟩,?_,hs⟩
  change (support (u.val+v.val)).card = 8
  rw [hs,card_union_of_disjoint hUV,hU,hV]

theorem companions_pair_octad (T : FourSet) (U V : Finset Omega)
    (hU : U ∈ tetradCompanions T) (hV : V ∈ tetradCompanions T) (hne : U ≠ V) :
    U ∪ V ∈ octads := by
  have hd : Disjoint U V := disjoint_left.mpr (fun p hpU hpV =>
    hne (companion_unique_at_point T U V hU hV p hpU hpV))
  exact octad_union_from_common_tetrad T.val U V (companion_disjoint T U hU)
    (companion_disjoint T V hV) hd (companion_card T U hU) (companion_card T V hV)
    (companion_union_octad T U hU) (companion_union_octad T V hV)

theorem completion_valid (T : FourSet) : IsUnorderedSextet (sextetCompletionParts T) := by
  classical
  refine ⟨completion_six_parts T,completion_part_card T,completion_partition T,?_⟩
  intro U hU V hV hne
  rcases mem_insert.mp hU with rfl | hU
  · rcases mem_insert.mp hV with rfl | hV
    · exact False.elim (hne rfl)
    · exact companion_union_octad T V hV
  · rcases mem_insert.mp hV with rfl | hV
    · rw [union_comm]; exact companion_union_octad T U hU
    · exact companions_pair_octad T U V hU hV hne

noncomputable def sextetCompletion (T : FourSet) : UnorderedSextet :=
  ⟨sextetCompletionParts T,completion_valid T⟩

theorem tetrad_mem_completion (T : FourSet) : T.val ∈ (sextetCompletion T).val := by
  classical
  exact mem_insert_self _ _

theorem sextet_eq_completion (S : UnorderedSextet) (T : FourSet) (hT : T.val ∈ S.val) :
    S = sextetCompletion T := by
  classical
  apply Subtype.ext
  apply eq_of_subset_of_card_le
  · intro U hU
    by_cases he : U = T.val
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert.mpr
      right
      have hd := S.prop.parts_disjoint hT hU (Ne.symm he)
      have ho := S.prop.pair_octads T.val hT U hU (Ne.symm he)
      apply (companion_mem T U).mpr
      refine ⟨T.val ∪ U,ho,subset_union_left,?_⟩
      ext p
      have hdis : p ∈ T.val → p ∈ U → False := fun h h' => disjoint_left.mp hd h h'
      simp only [mem_sdiff,mem_union]
      tauto
  · rw [S.prop.six_parts,(sextetCompletion T).prop.six_parts]

theorem unique_sextet_through_tetrad (T : FourSet) :
    ∃! S : UnorderedSextet, T.val ∈ S.val :=
  ⟨sextetCompletion T,tetrad_mem_completion T,fun S hS => sextet_eq_completion S T hS⟩

theorem completion_eq_iff (T U : FourSet) : sextetCompletion T = sextetCompletion U ↔
    U.val ∈ (sextetCompletion T).val := by
  constructor
  · intro h; rw [h]; exact tetrad_mem_completion U
  · intro h; exact sextet_eq_completion _ U h

end Atlas.Codes
