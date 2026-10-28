module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Layers
public import Mathlib.GroupTheory.Index

/-!
# The marked image W/S₂ in G.2.4

The map is the restriction of S→S/S₂ to W=U∩S. Its kernel is the
intersection W∩S₂, even though S₂ need not be a subgroup of W. Its image
therefore has order [W:W∩S₂]. These are the literal maps and indices
needed by the upper-module recognition and the order formula.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6–7), printed pp.334–335.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] (D : Setup G) (g : G)
  [((S₂ D g).subgroupOf (D.S g)).Normal]

/-- The original W projects onto its image in the actual upper section. -/
def upperMap : D.W g →* upperImage D g (D.W g) :=
  ((QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g))).comp
    (inclusion (show D.W g ≤ D.S g from inf_le_right))).codRestrict _
    (fun w => mem_map.mpr ⟨⟨w, w.property.2⟩, w.property, rfl⟩)

theorem upperMap_surjective : Function.Surjective (upperMap D g) := by
  intro q
  obtain ⟨s, hs, he⟩ := q.property
  exact ⟨⟨s, hs⟩, Subtype.ext he⟩

theorem upperMap_ker : (upperMap D g).ker = (S₂ D g).subgroupOf (D.W g) := by
  ext w
  change (⟨QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g))
    ⟨w, w.property.2⟩, _⟩ : upperImage D g (D.W g)) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

theorem card_upperImage_W : Nat.card (upperImage D g (D.W g)) =
    (S₂ D g).relIndex (D.W g) := by
  change Nat.card ((D.W g).subgroupOf (D.S g) |>.map
    (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  exact relIndex_subgroupOf (show D.W g ≤ D.S g from inf_le_right)

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
