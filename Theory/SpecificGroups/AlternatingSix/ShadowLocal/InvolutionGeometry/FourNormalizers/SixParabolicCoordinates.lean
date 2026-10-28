module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.ConjugacyClasses
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Compatible coordinates for the two A₆ parabolic types

The even relabelling `[4,5,0,2,3,1]` carries the standard incident
duad–syntheme flag to the normalizers of `standardFour` and `secondFour`.
Both identities use this same coordinate map. The tests reduce normalization
to preservation of the literal two-letter set or three-pair partition.

Source: Aschbacher–Smith, I.5, printed pp.419–422, and the diagram-action
step of 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal AlternatingSix.ShadowLocal.FourNormalizers
namespace AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics
local instance : Fintype (Equiv.Perm (Fin 6)) := fintypePerm
local instance : Fintype A6 := Subtype.fintype _

def coordinates : A6 :=
  ⟨Equiv.swap 0 4 * Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 1 5, by decide⟩

theorem coordinates_values : ∀ i : Fin 6, coordinates.val i = ![4,5,0,2,3,1] i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem standard_test (σ : Theory.SpecificGroups.SymmetricSix.S6) :
    σ * tailSwap = tailSwap * σ ↔
      coordinates.val⁻¹ * σ * coordinates.val ∈ Theory.SpecificGroups.SymmetricSix.duadStabilizer := by
  revert σ
  decide +kernel

theorem standard_normalizer_coordinates : normalizer (standardFour : Set A6) =
    (MulAut.conj coordinates).mapSubgroup Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer := by
  ext g
  rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe]
  change standardFour.map (permutationAction g.val).toMonoidHom = standardFour ↔ _
  rw [natural_stabilizes_standard_iff]
  change _ ↔ g ∈ Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.map (MulAut.conj coordinates).toMonoidHom
  rw [mem_map_equiv]
  exact standard_test g.val

theorem map_second_eq_iff (α : AutA6) :
    secondFour.map α.toMonoidHom = secondFour ↔
      ∀ i : V, ∃ j : V, secondEmbedding j = α (secondEmbedding i) := by
  constructor
  · intro h i
    change α (secondEmbedding i) ∈ secondFour
    rw [← h]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · intro h
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h i
    · rw [card_map_of_injective α.injective]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem second_test (σ : Theory.SpecificGroups.SymmetricSix.S6) :
    (∀ i : V, ∃ j : V, (secondEmbedding j).val =
      σ * (secondEmbedding i).val * σ⁻¹) ↔
      coordinates.val⁻¹ * σ * coordinates.val ∈ Theory.SpecificGroups.SymmetricSix.synthemeStabilizer := by
  revert σ
  decide +kernel

theorem second_normalizer_coordinates : normalizer (secondFour : Set A6) =
    (MulAut.conj coordinates).mapSubgroup Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer := by
  ext g
  rw [mem_normalizer_iff_map_conj_eq]
  change secondFour.map (MulAut.conj g).toMonoidHom = secondFour ↔
    g ∈ Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map (MulAut.conj coordinates).toMonoidHom
  rw [map_second_eq_iff, mem_map_equiv]
  simp only [Subtype.ext_iff]
  exact second_test g.val
end AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics
