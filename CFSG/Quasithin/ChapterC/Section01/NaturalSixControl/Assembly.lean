module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SmallImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.MSReduction

/-!
# The source C.1.37 point-parabolic reduction

The original natural S6 point-parabolic source now gives the literal
characteristic-normal alternative, an A6 block, or the original component--
Baumann MS pair. The small Thompson images use B.2.10 and C.1.24(c); the
full point-radical image uses B.2.19 and produces the actual MS2(a)/MS3
hypotheses. Applying the C.1.32 MS block terminal then removes the third
alternative and types the block on the original natural module coordinates.

The `MSBlockStatement` premise is exactly that remaining C.1.32 theorem;
its whole-core symplectic reconstruction is developed separately, not
assumed by any point-radical or Baumann calculation here.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and C.1.32,
printed pp.135--136.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open ChapterB ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
namespace SourceData
variable (d : SourceData L V T)
include d

/-- The original source reaches either its characteristic or block conclusion,
or the literal MS pair on the same component and Baumann subgroup. -/
theorem characteristic_or_block_or_intrinsicMSPair :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ IsAlternatingBlock L 6 ∨ IntrinsicMSPair d := by
  by_cases hs : (elementaryAbelianMaxJ d.R).map d.q0 ≤ last
  · rcases d.characteristic_or_block_of_small_thompson_image hs with hc | hb
    · exact Or.inl hc
    · exact Or.inr (Or.inl hb)
  by_cases hc : ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal
  · exact Or.inl hc
  exact Or.inr (Or.inr (d.intrinsicMSPair_of_full_image hs hc))

/-- In the original nonblock application, absence of a normal characteristic
subgroup constructs the exact MS pair required by C.1.32. -/
theorem intrinsicMSPair_of_no_characteristic_of_not_block
    (hc : ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) (hb : ¬ IsAlternatingBlock L 6) : IntrinsicMSPair d := by
  exact ((d.characteristic_or_block_or_intrinsicMSPair).resolve_left hc).resolve_left hb

/-- The C.1.37 alternative with its exact remaining C.1.32 MS terminal. -/
theorem characteristic_or_block_of_msBlock
    (hms : MSBlockStatement d) :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ IsAlternatingBlock L 6 := by
  by_cases hs : (elementaryAbelianMaxJ d.R).map d.q0 ≤ last
  · exact d.characteristic_or_block_of_small_thompson_image hs
  by_cases hc : ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal
  · exact Or.inl hc
  right
  have hp := d.intrinsicMSPair_of_full_image hs hc
  have hblock : IsBlock L := hms hp.radical hp.characteristic
  let := d.elementary
  exact RankOne.SymmetricSix.isAlternatingBlock_of_natural_six L V
    hblock d.q d.image_component d.eV d.action d.module_moved

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
