/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCounting

/-!
Golay automorphisms act on sextets and preserve tetrad completion.
Transport of partitions and octads defines the action; uniqueness of completion
proves equivariance. The final package assembles the proved geometry and counts.

Source: `Atlas/Mathieu/SextetAction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open Finset

theorem permuteBlock_injective (σ : Equiv.Perm Omega) : Function.Injective (permuteBlock σ) := by
  intro U V h
  have hh := congrArg (permuteBlock σ⁻¹) h
  simpa only [← permuteBlock_mul,inv_mul_cancel,permuteBlock_one] using hh

theorem permuteBlock_card (σ : Equiv.Perm Omega) (T : Finset Omega) :
    (permuteBlock σ T).card = T.card := card_image_of_injective T σ.injective

noncomputable def permuteSextetParts (σ : Equiv.Perm Omega) (S : Finset (Finset Omega)) :
    Finset (Finset Omega) := S.image (permuteBlock σ)

@[simp] theorem permuteSextetParts_one (S : Finset (Finset Omega)) : permuteSextetParts 1 S = S := by
  classical
  change S.image (permuteBlock 1) = S
  calc
    _ = S.image id := Finset.image_congr (fun U _ => permuteBlock_one U)
    _ = S := image_id

theorem permuteSextetParts_mul (σ τ : Equiv.Perm Omega) (S : Finset (Finset Omega)) :
    permuteSextetParts (σ*τ) S = permuteSextetParts σ (permuteSextetParts τ S) := by
  classical
  simp only [permuteSextetParts,image_image]
  apply Finset.image_congr
  intro U _
  exact permuteBlock_mul σ τ U

theorem permuteSextetParts_valid (g : Mathieu24CodeModel) (S : UnorderedSextet) :
    IsUnorderedSextet (permuteSextetParts g.val S.val) := by
  classical
  constructor
  · rw [permuteSextetParts,card_image_of_injective _ (permuteBlock_injective _),S.prop.six_parts]
  · intro U hU
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hU
    rw [permuteBlock_card]
    exact S.prop.tetrad_size T hT
  · intro p
    obtain ⟨T,hT,hu⟩ := S.prop.partition (g.val⁻¹ p)
    refine ⟨permuteBlock g.val T,⟨mem_image.mpr ⟨T,hT.1,rfl⟩,?_⟩,?_⟩
    · exact mem_image.mpr ⟨g.val⁻¹ p,hT.2,by simp⟩
    · intro V hV
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hV.1
      obtain ⟨q,hq,hqp⟩ := mem_image.mp hV.2
      have hq' : q = g.val⁻¹ p := (Equiv.eq_symm_apply _).mpr hqp
      have he := hu U ⟨hU,hq' ▸ hq⟩
      exact congrArg (permuteBlock g.val) he
  · intro U hU V hV hne
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hU
    obtain ⟨R,hR,rfl⟩ := mem_image.mp hV
    have hTR : T ≠ R := fun h => hne (congrArg (permuteBlock g.val) h)
    have ho := (codePreserving_octadPreserving g.val g.prop (T∪R)).mp (S.prop.pair_octads T hT R hR hTR)
    simpa only [permuteBlock,image_union] using ho

noncomputable def sextetAction (g : Mathieu24CodeModel) (S : UnorderedSextet) : UnorderedSextet :=
  ⟨permuteSextetParts g.val S.val,permuteSextetParts_valid g S⟩

@[simp] theorem sextetAction_one (S : UnorderedSextet) : sextetAction 1 S = S := by
  apply Subtype.ext
  exact permuteSextetParts_one S.val

theorem sextetAction_mul (g h : Mathieu24CodeModel) (S : UnorderedSextet) :
    sextetAction (g*h) S = sextetAction g (sextetAction h S) := by
  apply Subtype.ext
  exact permuteSextetParts_mul g.val h.val S.val

noncomputable instance : MulAction Mathieu24CodeModel UnorderedSextet where
  smul := sextetAction
  one_smul := sextetAction_one
  mul_smul := sextetAction_mul

def permuteFourSet (g : Mathieu24CodeModel) (T : FourSet) : FourSet :=
  ⟨permuteBlock g.val T.val,(permuteBlock_card _ _).trans T.prop⟩

theorem sextetCompletion_equivariant (g : Mathieu24CodeModel) (T : FourSet) :
    sextetCompletion (permuteFourSet g T) = sextetAction g (sextetCompletion T) := by
  symm
  apply sextet_eq_completion
  exact mem_image.mpr ⟨T.val,tetrad_mem_completion T,rfl⟩

structure SextetGeometryPackage : Prop where
  unique_completion : ∀ T : FourSet, ∃! S : UnorderedSextet, T.val ∈ S.val
  completion_fibers : ∀ S : UnorderedSextet, Nat.card {T : FourSet // sextetCompletion T = S} = 6
  incidence : (24 : ℕ).choose 4 = 6 * Nat.card UnorderedSextet
  count : Nat.card UnorderedSextet = 1771
  equivariant : ∀ (g : Mathieu24CodeModel) (T : FourSet),
    sextetCompletion (permuteFourSet g T) = sextetAction g (sextetCompletion T)
  labelled_bridge : ∀ S : Finset (Finset Omega), IsUnorderedSextet S ↔
    ∃ T : HexIndex → Finset Omega, IsSextet T ∧ labelledSextetParts T = S

theorem sextet_geometry_package : SextetGeometryPackage :=
  ⟨unique_sextet_through_tetrad,completion_fiber_card,sextet_incidence_count,
    unordered_sextets_card,sextetCompletion_equivariant,unordered_labelled_bridge⟩

end Atlas.Codes
