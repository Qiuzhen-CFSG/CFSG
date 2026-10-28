module
public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
/-!
# Faithful completions of a marked rank-two amalgam

A completion consists of injective endpoint maps agreeing on the marked common
subgroup, with images generating the ambient group. Compatible amalgam
isomorphisms change the marking without changing either image. Literal subgroup
inclusions provide the source-facing constructor.

When the endpoint orders have greatest common divisor equal to the middle
order, Lagrange's theorem forces their whole intersection to be the marked
middle image. This supplies the overlap needed by coset-cover arguments without
strengthening faithfulness to include an intersection assumption.

Source: Aschbacher--Smith, F.2.1 and F.4.4, printed pp.265 and 274.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R G : Type*} [Group L] [Group B] [Group R] [Group G]
variable (α : RankTwoAmalgam L B R)
/-- A completion injective on all three groups of a rank-two amalgam. -/
structure FaithfulCompletion where
  left : L →* G
  right : R →* G
  compatible : left.comp α.left = right.comp α.right
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  middle_injective : Function.Injective (left.comp α.left)
  generated : left.range ⊔ right.range = ⊤
namespace FaithfulCompletion
variable {α} (c : FaithfulCompletion α (G := G))
abbrev middle : B →* G := c.left.comp α.left

theorem middle_le_left : c.middle.range ≤ c.left.range := by
  rintro x ⟨b, rfl⟩
  exact ⟨α.left b, rfl⟩
theorem middle_le_right : c.middle.range ≤ c.right.range := by
  rintro x ⟨b, rfl⟩
  exact ⟨α.right b, (DFunLike.congr_fun c.compatible b).symm⟩
theorem left_card : Nat.card c.left.range = Nat.card L :=
  (Nat.card_congr (MonoidHom.ofInjective c.left_injective).toEquiv).symm
theorem right_card : Nat.card c.right.range = Nat.card R :=
  (Nat.card_congr (MonoidHom.ofInjective c.right_injective).toEquiv).symm
theorem middle_card : Nat.card c.middle.range = Nat.card B :=
  (Nat.card_congr (MonoidHom.ofInjective c.middle_injective).toEquiv).symm

/-- Coprime endpoint indices force the whole overlap, without an extra
intersection hypothesis on a completion. -/
theorem overlap_eq_of_gcd [Finite L] [Finite R] (h : (Nat.card L).gcd (Nat.card R) = Nat.card B) :
    c.left.range ⊓ c.right.range = c.middle.range := by
  have : Finite c.left.range := Finite.of_equiv L
    (MonoidHom.ofInjective c.left_injective).toEquiv
  have : Finite (c.left.range ⊓ c.right.range : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have : Finite c.middle.range := Finite.of_injective
    (Subgroup.inclusion c.middle_le_left) (Subgroup.inclusion_injective _)
  symm
  apply Subgroup.eq_of_le_of_card_ge (le_inf c.middle_le_left c.middle_le_right)
  have hd := Nat.dvd_gcd
    (Subgroup.card_dvd_of_le (show c.left.range ⊓ c.right.range ≤ c.left.range from inf_le_left))
    (Subgroup.card_dvd_of_le (show c.left.range ⊓ c.right.range ≤ c.right.range from inf_le_right))
  rw [c.left_card, c.right_card, h, ← c.middle_card] at hd
  exact Nat.le_of_dvd (Nat.card_pos (α := c.middle.range)) hd

variable {L' B' R' : Type*} [Group L'] [Group B'] [Group R']
variable {β : RankTwoAmalgam L' B' R'}

private theorem range_comp_equiv {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : Y →* Z) (e : X ≃* Y) : (f.comp e.toMonoidHom).range = f.range := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp⟩

/-- Change the marked amalgam using both commuting squares. -/
def comapIso (d : FaithfulCompletion β (G := G)) (e : Iso α β) :
    FaithfulCompletion α (G := G) where
  left := d.left.comp e.left.toMonoidHom
  right := d.right.comp e.right.toMonoidHom
  compatible := by
    ext b
    change d.left (e.left (α.left b)) = d.right (e.right (α.right b))
    rw [e.left_commutes, e.right_commutes]
    exact DFunLike.congr_fun d.compatible _
  left_injective := d.left_injective.comp e.left.injective
  right_injective := d.right_injective.comp e.right.injective
  middle_injective := by
    intro x y hxy
    apply e.middle.injective
    apply d.middle_injective
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.left_commutes] using hxy
  generated := by
    rw [range_comp_equiv, range_comp_equiv]
    exact d.generated

@[simp] theorem comapIso_left_range (d : FaithfulCompletion β (G := G)) (e : Iso α β) :
    (d.comapIso e).left.range = d.left.range := range_comp_equiv _ _
@[simp] theorem comapIso_right_range (d : FaithfulCompletion β (G := G)) (e : Iso α β) :
    (d.comapIso e).right.range = d.right.range := range_comp_equiv _ _

@[simp] theorem comapIso_middle_range (d : FaithfulCompletion β (G := G)) (e : Iso α β) :
    (d.comapIso e).middle.range = d.middle.range := by
  have hh : (d.comapIso e).middle = d.middle.comp e.middle.toMonoidHom := by
    ext b
    exact congrArg d.left (e.left_commutes b)
  rw [hh]
  exact range_comp_equiv _ _

/-- The literal subgroup inclusion completion, with generation as its only
additional condition. -/
def ofSubgroups (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤) : FaithfulCompletion (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂)
      (G := G) where
  left := P₁.subtype
  right := P₂.subtype
  compatible := rfl
  left_injective := Subtype.val_injective
  right_injective := Subtype.val_injective
  middle_injective := Subtype.val_injective
  generated := by simpa only [Subgroup.range_subtype] using hgen

@[simp] theorem ofSubgroups_left_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁)
    (h₂ : T ≤ P₂) (hgen : P₁ ⊔ P₂ = ⊤) :
    (ofSubgroups P₁ T P₂ h₁ h₂ hgen).left.range = P₁ := P₁.range_subtype
@[simp] theorem ofSubgroups_right_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁)
    (h₂ : T ≤ P₂) (hgen : P₁ ⊔ P₂ = ⊤) :
    (ofSubgroups P₁ T P₂ h₁ h₂ hgen).right.range = P₂ := P₂.range_subtype
@[simp] theorem ofSubgroups_middle_range (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁)
    (h₂ : T ≤ P₂) (hgen : P₁ ⊔ P₂ = ⊤) :
    (ofSubgroups P₁ T P₂ h₁ h₂ hgen).middle.range = T := T.range_subtype
end FaithfulCompletion
end Theory.GroupTheory.RankTwoAmalgam
