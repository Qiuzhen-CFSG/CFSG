/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24PointOrders

/-!
# Mathieu24NotSixTransitive

The Golay coordinate action is not six-homogeneous and hence not six-transitive. Two
six-sets are distinguished by containment in an octad, an invariant preserved by every
code automorphism.

Source: `Atlas/Mathieu/Mathieu24NotSixTransitive.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

/-- Incidence with an octad is preserved by the actual full code automorphism group. -/
def ContainedInOctad (T : Finset Omega) : Prop := ∃ O ∈ octads, T ⊆ O

theorem containedInOctad_permute (g : Mathieu24CodeModel) (T : Finset Omega)
    (hT : ContainedInOctad T) : ContainedInOctad (permuteBlock g.val T) := by
  obtain ⟨O,hO,hTO⟩ := hT
  exact ⟨permuteBlock g.val O,(codePreserving_octadPreserving g.val g.prop O).mp hO,
    image_subset_image hTO⟩

/-- The Steiner property distinguishes two six-subset orbits geometrically. -/
theorem sixSet_octad_obstruction : ∃ U V : Finset Omega,
    U.card = 6 ∧ V.card = 6 ∧ ContainedInOctad U ∧ ¬ ContainedInOctad V := by
  classical
  obtain ⟨F,_,hF⟩ := exists_subset_card_eq (s := (univ : Finset Omega)) (n := 5)
    (by norm_num [Omega,HexIndex])
  obtain ⟨O,⟨hO,hFO⟩,_⟩ := octad_steiner F hF
  have ho := octad_size O hO
  obtain ⟨a,ha,haF⟩ := exists_mem_notMem_of_card_lt_card (s := F) (t := O) (by omega)
  obtain ⟨b,_,hb⟩ := exists_mem_notMem_of_card_lt_card (s := O) (t := (univ : Finset Omega))
    (by rw [ho]; norm_num [Omega,HexIndex])
  have hbF : b ∉ F := fun h => hb (hFO h)
  refine ⟨insert a F,insert b F,by simp [haF,hF],by simp [hbF,hF],
    ⟨O,hO,insert_subset ha hFO⟩,?_⟩
  rintro ⟨P,hP,hFP⟩
  have he : P = O := octad_unique_on_five F P O hF hP hO
    (subset_trans (subset_insert _ _) hFP) hFO
  exact hb (he ▸ hFP (mem_insert_self _ _))

theorem mathieu24_not_six_homogeneous : ∃ U V : Finset Omega,
    U.card = 6 ∧ V.card = 6 ∧ ∀ g : Mathieu24CodeModel, permuteBlock g.val U ≠ V := by
  obtain ⟨U,V,hU,hV,hu,hv⟩ := sixSet_octad_obstruction
  refine ⟨U,V,hU,hV,?_⟩
  intro g he
  exact hv (he ▸ containedInOctad_permute g U hu)

def finiteSetLabelling {k : ℕ} (T : Finset Omega) (hT : T.card = k) : Fin k ≃ {p // p ∈ T} := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin,Fintype.card_coe,hT]

def finiteSetEmbedding {k : ℕ} (T : Finset Omega) (hT : T.card = k) : Fin k ↪ Omega :=
  (finiteSetLabelling T hT).toEmbedding.trans (Function.Embedding.subtype _)

theorem finiteSetEmbedding_image {k : ℕ} (T : Finset Omega) (hT : T.card = k) :
    univ.image (finiteSetEmbedding T hT) = T := by
  classical
  ext p
  constructor
  · rintro hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    exact (finiteSetLabelling T hT i).prop
  · intro hp
    obtain ⟨i,hi⟩ := (finiteSetLabelling T hT).surjective ⟨p,hp⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

theorem mathieu24_not_six_transitive : ¬ MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 6 := by
  intro ht
  classical
  obtain ⟨U,V,hU,hV,hUV⟩ := mathieu24_not_six_homogeneous
  obtain ⟨g,hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp ht)
    (finiteSetEmbedding U hU) (finiteSetEmbedding V hV)
  apply hUV g
  have hf : g.val ∘ finiteSetEmbedding U hU = finiteSetEmbedding V hV := by
    funext i
    exact congrArg (fun e : Fin 6 ↪ Omega => e i) hg
  change U.image g.val = V
  rw [← finiteSetEmbedding_image U hU,image_image,hf,finiteSetEmbedding_image]

end Atlas.Codes
