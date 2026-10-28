module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree

/-!
# Normal targets of the cubic commutator module

The module of an A₃ block is minimal normal and its central layer is trivial.
If one nonidentity module element maps into a normal subgroup, its entire
module does. This is used for the two actual inner four-groups in the
component inspection of Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B]

/-- One nonidentity module element in a normal target forces the full module image into it. -/
theorem IsAlternatingBlock.module_image_le_normal_of_nontrivial
    (h : IsAlternatingBlock A 3) (f : A →* B) (N : Subgroup B) [N.Normal]
    (a : A) (ha : a ∈ blockU A) (hm : a ≠ 1) (hfa : f a ∈ N) :
    (blockU A).map f ≤ N := by
  have hz : blockU A ⊓ center A = ⊥ := by rw [h.center_eq_bot,inf_bot_eq]
  have hn : (N.comap f ⊓ blockU A).Normal := inferInstance
  rcases h.2.1.irreducible.2 (N.comap f ⊓ blockU A) hn
      (by rw [hz]; exact bot_le) inf_le_right with hi | hi
  · have hh : a ∈ (⊥ : Subgroup A) := hi.trans hz ▸ ⟨hfa,ha⟩
    exact (hm hh).elim
  · exact map_le_iff_le_comap.mpr (hi ▸ inf_le_left)
end CFSG.Quasithin.ChapterC

