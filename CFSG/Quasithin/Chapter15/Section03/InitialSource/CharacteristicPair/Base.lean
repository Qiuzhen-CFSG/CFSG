module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import Stellmacher.BaumannMap

/-!
# The actual Baumann base for the universal characteristic-pair theorem

For the original Sylow T, B = Baum(T) is a nontrivial two-group fixed by
the Baumann operator. Nontriviality comes from the actual nontrivial
local two-core and the central involutions of T. Injective Baumann
transport and B.2.3(4) establish fixedness in the intrinsic group B.

Given the full universal C.1.18 theorem, one pair is chosen on this B
before quantifying over every marked local group H. The C.1.19
restriction yields the actual pair on T, and its C₂ normalizer has a
maximal two-local overgroup Mf containing T.

The universal existence theorem remains an explicit earlier source input.
A merely structural pair never supplies its universal alternatives.
The later control conclusions of 14.1.11–12 are not asserted here.

Source: Aschbacher–Smith C.1.18–20, printed pp.126–127, and the
characteristic subgroup and choice preceding 14.1.12, pp.978–979.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
open ChapterC ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_baumann_ne_bot (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    ChapterB.baumann (⊤ : Subgroup T) ≠ ⊥ := by
  let B := ChapterB.baumann (⊤ : Subgroup T)
  have hZB : centralInvolutions T ≤ B.map (T : Subgroup G).subtype := by
    intro z hz
    have hs := (mem_omegaOneCenterAmbient_iff _ z).mp hz
    refine ⟨⟨z, hs.1⟩, ⟨mem_top _, ?_⟩, rfl⟩
    intro a _
    exact Subtype.ext (hs.2.2 a a.property)
  intro hB
  have hmap : B.map (T : Subgroup G).subtype = ⊥ := by rw [show B = ⊥ from hB, Subgroup.map_bot]
  exact centralInvolutions_ne_bot_of_maximal_local T hM (bot_unique (hZB.trans_eq hmap))

theorem source_baumann_isBaumannFixed (T : Sylow 2 G) :
    IsBaumannFixed (ChapterB.baumann (⊤ : Subgroup T)) := by
  let B := ChapterB.baumann (⊤ : Subgroup T)
  have hmap : (ChapterB.baumann (⊤ : Subgroup B)).map B.subtype = ChapterB.baumann B := by
    simpa only [ChapterB.baumann, ChapterB.thompsonAlpha, ← MonoidHom.range_eq_map, range_subtype] using
      baumann_map_injective B.subtype B.subtype_injective (⊤ : Subgroup B)
  have hher : B = ChapterB.baumann B := ChapterB.lemma_B_2_3_4 (⊤ : Subgroup T) B le_rfl le_top
  apply (map_injective B.subtype_injective)
  rw [hmap, ← MonoidHom.range_eq_map, range_subtype]
  exact hher.symm

/-- The exact three hypotheses of the universal C.1.18 producer. -/
theorem source_baumann_existence_domain (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    IsPGroup 2 (ChapterB.baumann (⊤ : Subgroup T)) ∧
      Nontrivial (ChapterB.baumann (⊤ : Subgroup T)) ∧
      IsBaumannFixed (ChapterB.baumann (⊤ : Subgroup T)) :=
  ⟨T.isPGroup'.to_subgroup _, (nontrivial_iff_ne_bot _).mpr (source_baumann_ne_bot T hM),
    source_baumann_isBaumannFixed T⟩

/-- Literal source consumer, conditional on the full earlier universal theorem.
A structural pair alone is never used as an existence substitute. -/
theorem source_characteristic_pair_of_universal
    (hGN : ∀ (B : Type u) [Group B] [Finite B] [Nontrivial B],
      IsPGroup 2 B → IsBaumannFixed B →
      ∃ D : CharacteristicPair B, ∀ (H : Type u) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives D.first D.second e)
    (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    let B := ChapterB.baumann (⊤ : Subgroup T)
    ∃ C : RankOneCharacteristicPair B,
      C.first.map (T : Subgroup G).subtype ≤ centralInvolutions T ∧
      ∀ (H : Type u) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives (C.first.subgroupOf B) C.second e := by
  let B := ChapterB.baumann (⊤ : Subgroup T)
  obtain ⟨hp, hn, hf⟩ := source_baumann_existence_domain T hM
  let : Nontrivial B := hn
  obtain ⟨D, hD⟩ := hGN B hp hf
  let := D.first_characteristic
  let := D.second_characteristic
  let : B.Characteristic := ChapterB.baumann_characteristic
  let C := glaubermanNiles_reducePair T.isPGroup' B D.first D.second
    D.first_ne_bot D.second_ne_bot D.first_le_omegaCenter
  refine ⟨C, map_mono C.first_le_omega, ?_⟩
  intro H _ _ e he
  rcases hD H e he with hc | hn | hb
  · exact Or.inl ((map_mono (centerRestriction_subgroupOf_le B D.first)).trans hc)
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr hb)


/-- The actual C₂ normalizer has a maximal two-local overgroup containing T.
This is the choice preceding 14.1.12, without its later control conclusions. -/
theorem characteristic_pair_normalizer_overgroup (T : Sylow 2 G)
    (C : RankOneCharacteristicPair (ChapterB.baumann (⊤ : Subgroup T))) :
    ∃ Mf ∈ maximalTwoLocalOvergroups (T : Subgroup G),
      normalizer (C.second.map ((T : Subgroup G).subtype.comp
        (ChapterB.baumann (⊤ : Subgroup T)).subtype) : Set G) ≤ Mf := by
  let B := ChapterB.baumann (⊤ : Subgroup T)
  let : B.Characteristic := ChapterB.baumann_characteristic
  let : (C.second.map B.subtype).Characteristic := C.second_image_characteristic
  let D := C.second.map B.subtype
  let D₂ := D.map (T : Subgroup G).subtype
  have hn : D₂ ≠ ⊥ := fun h => C.second_image_ne_bot
    ((D.map_eq_bot_iff_of_injective (T : Subgroup G).subtype_injective).mp h)
  have hp : IsPGroup 2 D₂ := (T.isPGroup'.to_subgroup D).map (T : Subgroup G).subtype
  have hTN : (T : Subgroup G) ≤ normalizer (D₂ : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      D.le_normalizer_map (T : Subgroup G).subtype
  obtain ⟨Mf, hMf, hm⟩ := Finite.exists_le_maximal (show IsTwoLocal (normalizer (D₂ : Set G)) from
    ⟨D₂, hn, hp, rfl⟩)
  refine ⟨Mf, ⟨hm, hTN.trans hMf⟩, ?_⟩
  simpa only [D₂, D, Subgroup.map_map] using hMf

end CFSG.Quasithin.Chapter15.Section03.InitialSource
