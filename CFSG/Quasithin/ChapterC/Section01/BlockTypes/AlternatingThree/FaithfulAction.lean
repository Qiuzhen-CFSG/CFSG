module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree

/-!
# Faithful actions of a cubic block

The four-element module of an A₃ block is minimal normal and self
centralizing. A nontrivial action on any one of its elements therefore has
trivial kernel on the entire block. This supplies the actual faithful A₄
action in Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B] [Finite A]

/-- Moving one nontrivial module element makes an action of an A₃ block
faithful. This retains the actual block and commutator module. -/
theorem IsAlternatingBlock.injective_of_moves_module
    (h : IsAlternatingBlock A 3) (f : A →* B)
    (a : A) (ha : a ∈ blockU A) (hm : f a ≠ 1) : Function.Injective f := by
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hcore : pCore 2 A = blockU A := h.2.1.core_eq_blockU_of_quotient_three hc
  have hz : blockU A ⊓ center A = ⊥ := by rw [h.center_eq_bot,inf_bot_eq]
  have hcent : centralizer (blockU A : Set A) ≤ blockU A := by
    rw [←hcore,←h.2.1.fitting]
    exact centralizer_generalizedFitting_le A
  apply f.ker_eq_bot_iff.mp
  rcases h.2.1.irreducible.2 (f.ker ⊓ blockU A) inferInstance (by rw [hz]; exact bot_le)
    inf_le_right with hi | hi
  · have he : f.ker ⊓ blockU A = ⊥ := hi.trans hz
    have hh : ⁅f.ker,blockU A⁆ = ⊥ := bot_unique
      ((le_inf (commutator_le_left _ _) (commutator_le_right _ _)).trans he.le)
    have hker := (commutator_eq_bot_iff_le_centralizer.mp hh).trans hcent
    exact (inf_eq_left.mpr hker).symm.trans he
  · exact (hm ((show a ∈ f.ker ⊓ blockU A from hi.symm ▸ ha).1)).elim

end CFSG.Quasithin.ChapterC

