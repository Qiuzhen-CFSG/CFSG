module

public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Rank-two amalgams and parabolic equivalence

A rank-two amalgam is a pair of homomorphisms with common domain. An
isomorphism must commute with both homomorphisms. Parabolic equivalence only
identifies the three groups, without imposing either commuting square.

The distinction is needed in the rank-two recognition theorem: its two Hall--
Janko alternatives assert only parabolic equivalence. The constructions below
use composition and inversion of the three group isomorphisms; compatibility
of the inverse follows by applying the original isomorphism to each square.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Definitions F.1.4--F.1.5 and Notation F.1.11, printed pp. 260--262.
-/

@[expose] public section

namespace Theory.GroupTheory

/-- Two homomorphisms with a common domain. Injectivity is not part of
Definition F.1.4; subgroup amalgams have injective structure maps. -/
structure RankTwoAmalgam (L B R : Type*) [Group L] [Group B] [Group R] where
  left : B →* L
  right : B →* R

namespace RankTwoAmalgam

variable {L B R L' B' R' L'' B'' R'' : Type*}
  [Group L] [Group B] [Group R]
  [Group L'] [Group B'] [Group R']
  [Group L''] [Group B''] [Group R'']

/-- Isomorphisms of the three parabolic groups, without compatibility. -/
structure ParabolicEquiv (α : RankTwoAmalgam L B R)
    (β : RankTwoAmalgam L' B' R') where
  left : L ≃* L'
  middle : B ≃* B'
  right : R ≃* R'

/-- An isomorphism of amalgams, including both commuting squares. -/
structure Iso (α : RankTwoAmalgam L B R)
    (β : RankTwoAmalgam L' B' R') extends ParabolicEquiv α β where
  left_commutes : ∀ b, left (α.left b) = β.left (middle b)
  right_commutes : ∀ b, right (α.right b) = β.right (middle b)

variable {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
  {γ : RankTwoAmalgam L'' B'' R''}

namespace ParabolicEquiv

def refl (α : RankTwoAmalgam L B R) : ParabolicEquiv α α :=
  ⟨MulEquiv.refl L, MulEquiv.refl B, MulEquiv.refl R⟩

def symm (e : ParabolicEquiv α β) : ParabolicEquiv β α :=
  ⟨e.left.symm, e.middle.symm, e.right.symm⟩

def trans (e : ParabolicEquiv α β) (f : ParabolicEquiv β γ) :
    ParabolicEquiv α γ :=
  ⟨e.left.trans f.left, e.middle.trans f.middle, e.right.trans f.right⟩

end ParabolicEquiv

namespace Iso

def refl (α : RankTwoAmalgam L B R) : Iso α α where
  toParabolicEquiv := ParabolicEquiv.refl α
  left_commutes _ := rfl
  right_commutes _ := rfl

def symm (e : Iso α β) : Iso β α where
  toParabolicEquiv := e.toParabolicEquiv.symm
  left_commutes b := by
    change e.left.symm (β.left b) = α.left (e.middle.symm b)
    apply e.left.injective
    simpa using (e.left_commutes (e.middle.symm b)).symm
  right_commutes b := by
    change e.right.symm (β.right b) = α.right (e.middle.symm b)
    apply e.right.injective
    simpa using (e.right_commutes (e.middle.symm b)).symm

def trans (e : Iso α β) (f : Iso β γ) : Iso α γ where
  toParabolicEquiv := e.toParabolicEquiv.trans f.toParabolicEquiv
  left_commutes b := by
    change f.left (e.left (α.left b)) = γ.left (f.middle (e.middle b))
    rw [e.left_commutes, f.left_commutes]
  right_commutes b := by
    change f.right (e.right (α.right b)) = γ.right (f.middle (e.middle b))
    rw [e.right_commutes, f.right_commutes]

/-- The left structure map stays injective under amalgam isomorphism. -/
theorem left_injective_iff (e : Iso α β) :
    Function.Injective α.left ↔ Function.Injective β.left := by
  constructor
  · intro h x y hxy
    apply e.middle.symm.injective
    apply h
    apply e.left.injective
    simpa only [e.left_commutes, e.middle.apply_symm_apply] using hxy
  · intro h x y hxy
    apply e.middle.injective
    apply h
    simpa only [← e.left_commutes] using congrArg e.left hxy

/-- The right structure map stays injective under amalgam isomorphism. -/
theorem right_injective_iff (e : Iso α β) :
    Function.Injective α.right ↔ Function.Injective β.right := by
  constructor
  · intro h x y hxy
    apply e.middle.symm.injective
    apply h
    apply e.right.injective
    simpa only [e.right_commutes, e.middle.apply_symm_apply] using hxy
  · intro h x y hxy
    apply e.middle.injective
    apply h
    simpa only [← e.right_commutes] using congrArg e.right hxy

end Iso

/-- The inclusion amalgam of three subgroups. The usual subgroup amalgam
uses `B = P₁ ⊓ P₂`; stating just containment also permits subamalgams. -/
def ofSubgroups {G : Type*} [Group G] (P₁ B P₂ : Subgroup G)
    (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) : RankTwoAmalgam P₁ B P₂ :=
  ⟨Subgroup.inclusion h₁, Subgroup.inclusion h₂⟩

theorem ofSubgroups_left_injective {G : Type*} [Group G]
    (P₁ B P₂ : Subgroup G) (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) :
    Function.Injective (ofSubgroups P₁ B P₂ h₁ h₂).left :=
  Subgroup.inclusion_injective h₁

theorem ofSubgroups_right_injective {G : Type*} [Group G]
    (P₁ B P₂ : Subgroup G) (h₁ : B ≤ P₁) (h₂ : B ≤ P₂) :
    Function.Injective (ofSubgroups P₁ B P₂ h₁ h₂).right :=
  Subgroup.inclusion_injective h₂

end RankTwoAmalgam
end Theory.GroupTheory
