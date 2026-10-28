/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayAutomorphisms

/-!
Unordered sextets and their equivalence with labelled sextets.
The partition axioms give disjointness and injectivity; choosing a labelling
of the six parts proves the bridge in both directions.

Source: `Atlas/Mathieu/UnorderedSextets.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open Finset
open scoped BigOperators

/-- An unordered six-part partition, with the octad-union property. -/
structure IsUnorderedSextet (S : Finset (Finset Omega)) : Prop where
  six_parts : S.card = 6
  tetrad_size : ∀ T ∈ S, T.card = 4
  partition : ∀ p : Omega, ∃! T : Finset Omega, T ∈ S ∧ p ∈ T
  pair_octads : ∀ T ∈ S, ∀ U ∈ S, T ≠ U → T ∪ U ∈ octads

abbrev UnorderedSextet := {S : Finset (Finset Omega) // IsUnorderedSextet S}
abbrev FourSet := {T : Finset Omega // T.card = 4}

theorem IsUnorderedSextet.parts_disjoint {S : Finset (Finset Omega)} (hS : IsUnorderedSextet S)
    {T U : Finset Omega} (hT : T ∈ S) (hU : U ∈ S) (hne : T ≠ U) : Disjoint T U := by
  apply disjoint_left.mpr
  intro p hp hq
  exact hne ((hS.partition p).unique ⟨hT,hp⟩ ⟨hU,hq⟩)

theorem IsSextet.injective {T : HexIndex → Finset Omega} (hT : IsSextet T) : Function.Injective T := by
  intro i j hij
  have hn : (T i).Nonempty := card_pos.mp (by rw [hT.tetrad_size]; decide)
  obtain ⟨p,hp⟩ := hn
  exact (hT.partition p).unique hp (hij ▸ hp)

noncomputable def labelledSextetParts (T : HexIndex → Finset Omega) : Finset (Finset Omega) := univ.image T

theorem labelledSextetParts_valid (T : HexIndex → Finset Omega) (hT : IsSextet T) :
    IsUnorderedSextet (labelledSextetParts T) := by
  classical
  constructor
  · rw [labelledSextetParts,card_image_of_injective _ hT.injective]
    norm_num [HexIndex]
  · intro U hU
    obtain ⟨i,_,rfl⟩ := mem_image.mp hU
    exact hT.tetrad_size i
  · intro p
    obtain ⟨i,hi,hu⟩ := hT.partition p
    refine ⟨T i,⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,hi⟩,?_⟩
    intro U hU
    obtain ⟨j,_,rfl⟩ := mem_image.mp hU.1
    exact congrArg T (hu j hU.2)
  · intro U hU V hV hne
    obtain ⟨i,_,rfl⟩ := mem_image.mp hU
    obtain ⟨j,_,rfl⟩ := mem_image.mp hV
    exact hT.pair_octads i j (fun h => hne (congrArg T h))

noncomputable def distinguishedUnorderedSextet : UnorderedSextet :=
  ⟨labelledSextetParts tetrad,labelledSextetParts_valid tetrad distinguished_sextet⟩

noncomputable def sextetLabelling (S : UnorderedSextet) : HexIndex ≃ {T // T ∈ S.val} := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_coe,S.prop.six_parts]
  norm_num [HexIndex]

noncomputable def labelSextet (S : UnorderedSextet) (i : HexIndex) : Finset Omega :=
  (sextetLabelling S i).val

theorem labelSextet_parts (S : UnorderedSextet) : labelledSextetParts (labelSextet S) = S.val := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨i,_,rfl⟩ := mem_image.mp hT
    exact (sextetLabelling S i).prop
  · intro hT
    obtain ⟨i,hi⟩ := (sextetLabelling S).surjective ⟨T,hT⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

theorem labelSextet_valid (S : UnorderedSextet) : IsSextet (labelSextet S) := by
  constructor
  · intro i; exact S.prop.tetrad_size _ (sextetLabelling S i).prop
  · intro p
    obtain ⟨T,hT,hu⟩ := S.prop.partition p
    obtain ⟨i,hi⟩ := (sextetLabelling S).surjective ⟨T,hT.1⟩
    have hi' : labelSextet S i = T := congrArg Subtype.val hi
    refine ⟨i,by dsimp only; rw [hi']; exact hT.2,?_⟩
    intro j hj
    apply (sextetLabelling S).injective
    apply Subtype.ext
    exact (hu (labelSextet S j) ⟨(sextetLabelling S j).prop,hj⟩).trans hi'.symm
  · intro i j hij
    apply S.prop.pair_octads _ (sextetLabelling S i).prop _ (sextetLabelling S j).prop
    intro h
    exact hij ((sextetLabelling S).injective (Subtype.ext h))

theorem unordered_labelled_bridge (S : Finset (Finset Omega)) : IsUnorderedSextet S ↔
    ∃ T : HexIndex → Finset Omega, IsSextet T ∧ labelledSextetParts T = S := by
  constructor
  · intro hS
    exact ⟨labelSextet ⟨S,hS⟩,labelSextet_valid _,labelSextet_parts _⟩
  · rintro ⟨T,hT,rfl⟩
    exact labelledSextetParts_valid T hT

theorem labelledSextetParts_relabel (T : HexIndex → Finset Omega) (σ : Equiv.Perm HexIndex) :
    labelledSextetParts (T ∘ σ) = labelledSextetParts T := by
  classical
  ext U
  simp only [labelledSextetParts,mem_image,mem_univ,true_and,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨σ i,hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨j,rfl⟩ := σ.surjective i
    exact ⟨j,hi⟩

end Atlas.Codes
