module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Layers
public import Mathlib.GroupTheory.Index

/-!
# The literal image W/S₃ in G.2.5

The upper marked summand is the image of W in S/S₃. Its projection has
kernel W∩S₃, and its order is the corresponding relative index in W.
The pair-product identity identifies that kernel with the two pair
intersections containing W. No inclusion S₃≤W is used.

Relative normality of S₃ in S is kept explicit until the root-action
argument constructs it. These maps and counting identities will then
apply to the precise quotient used by the source recognition theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(7–8), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree

variable {G : Type*} [Group G] (D : Setup G) (g h : G)
  [((S₃ D g h).subgroupOf (S D g h)).Normal]

/-- Projection from the original W onto its image in the upper layer. -/
def upperMap : W D g h →* upperImage D g h (W D g h) :=
  ((QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))).comp
    (inclusion (show W D g h ≤ S D g h from inf_le_right))).codRestrict _
    (fun w => mem_map.mpr ⟨⟨w, w.property.2⟩, w.property, rfl⟩)

theorem upperMap_surjective : Function.Surjective (upperMap D g h) := by
  intro q
  obtain ⟨s, hs, he⟩ := q.property
  exact ⟨⟨s, hs⟩, Subtype.ext he⟩

theorem upperMap_ker : (upperMap D g h).ker = (S₃ D g h).subgroupOf (W D g h) := by
  ext w
  change (⟨QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))
    ⟨w, w.property.2⟩, _⟩ : upperImage D g h (W D g h)) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

theorem card_upperImage_W : Nat.card (upperImage D g h (W D g h)) =
    (S₃ D g h).relIndex (W D g h) := by
  change Nat.card ((W D g h).subgroupOf (S D g h) |>.map
    (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  exact relIndex_subgroupOf (show W D g h ≤ S D g h from inf_le_right)

namespace Hypothesis
variable [Finite G] {D g h} {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- The marked upper summand is counted modulo the two pair intersections
inside W. Invariance and module recognition will determine its value 2^(nr). -/
theorem card_upperImage_pair_index (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hLI : D.L ≤ I D g h) :
    Nat.card (upperImage D g h (W D g h)) =
      ((W D g h ⊓ Setup.conjugate (W D g h) g) ⊔
        (W D g h ⊓ Setup.conjugate (W D g h) h)).relIndex (W D g h) := by
  rw [card_upperImage_W, ← inf_relIndex_left, d.W_inf_S₃ hUT hf hLI]

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
