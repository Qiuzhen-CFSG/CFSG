module
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Whole overlap and reversal of a generated completion

The completion in the join of two literal subgroups has their full
intersection as its marked middle image. The proof uses the public equations
of the generated-completion constructor. Reversing a completion exchanges
both endpoint maps and retains its middle map and whole-overlap equality.

Source application: Aschbacher–Smith F.4.4, printed p.274, with the actual
normalizer pair in 5.3, printed pp.657–659 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
open Subgroup
variable {G : Type*} [Group G]

@[simp] theorem ofGeneratedSubgroups_middle_range (P₁ T P₂ : Subgroup G)
    (h₁ : T ≤ P₁) (h₂ : T ≤ P₂) :
    (ofGeneratedSubgroups P₁ T P₂ h₁ h₂).middle.range = T.subgroupOf (P₁ ⊔ P₂) :=
by
  apply Subgroup.map_injective (P₁ ⊔ P₂).subtype_injective
  rw [MonoidHom.map_range, map_subgroupOf_eq_of_le (h₁.trans le_sup_left)]
  have he : (P₁ ⊔ P₂).subtype.comp
      (ofGeneratedSubgroups P₁ T P₂ h₁ h₂).middle = T.subtype := by
    ext t
    exact ofGeneratedSubgroups_left P₁ T P₂ h₁ h₂ (inclusion h₁ t)
  rw [he,range_subtype]

theorem ofGeneratedSubgroups_overlap (P₁ P₂ : Subgroup G) :
    (ofGeneratedSubgroups P₁ (P₁ ⊓ P₂) P₂ inf_le_left inf_le_right).left.range ⊓
      (ofGeneratedSubgroups P₁ (P₁ ⊓ P₂) P₂ inf_le_left inf_le_right).right.range =
      (ofGeneratedSubgroups P₁ (P₁ ⊓ P₂) P₂ inf_le_left inf_le_right).middle.range := by
  rw [ofGeneratedSubgroups_left_range, ofGeneratedSubgroups_right_range,
    ofGeneratedSubgroups_middle_range]
  exact (Subgroup.comap_inf _ _ _).symm

variable {L B R : Type*} [Group L] [Group B] [Group R]
variable {α : RankTwoAmalgam L B R}

def reverse (c : FaithfulCompletion α (G := G)) : FaithfulCompletion α.reverse (G := G) where
  left := c.right
  right := c.left
  compatible := c.compatible.symm
  left_injective := c.right_injective
  right_injective := c.left_injective
  middle_injective := by
    change Function.Injective (c.right.comp α.right)
    rw [← c.compatible]
    exact c.middle_injective
  generated := (sup_comm _ _).trans c.generated

@[simp] theorem reverse_left (c : FaithfulCompletion α (G := G)) : c.reverse.left = c.right := rfl
@[simp] theorem reverse_right (c : FaithfulCompletion α (G := G)) : c.reverse.right = c.left := rfl
@[simp] theorem reverse_middle (c : FaithfulCompletion α (G := G)) : c.reverse.middle = c.middle :=
  c.compatible.symm

theorem reverse_overlap (c : FaithfulCompletion α (G := G))
    (h : c.left.range ⊓ c.right.range = c.middle.range) :
    c.reverse.left.range ⊓ c.reverse.right.range = c.reverse.middle.range := by
  rw [reverse_left,reverse_right,reverse_middle,inf_comm,h]
end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
