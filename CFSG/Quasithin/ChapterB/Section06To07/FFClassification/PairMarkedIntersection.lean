module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural

/-!
# Intersections with marked product axes

A marked product identifies each original factor with one literal coordinate
axis.  Consequently the image of an arbitrary product subgroup intersected
with either marked factor is the corresponding coordinate intersection.  This
small transport lemma is used by the paired symmetric-five Baumann assembly.

Source: Aschbacher--Smith E.2.3, pp.216--217.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V D M : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Group D] [AddCommGroup M] [Module (ZMod 2) M]
variable {K : Type*} [Group K] {σ : Representation (ZMod 2) K V}
variable {d : SourceTwoFactorCase σ} {τ : Representation (ZMod 2) D M}

/-- The second-coordinate intersection in marked product coordinates. -/
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.map_inf_second
    (c : d.MarkedProduct τ) (F₁ F₂ : Subgroup D) :
    (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.second).map
      c.action.groupEquiv.toMonoidHom) = (⊥ : Subgroup D).prod F₂ := by
  calc
    (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.second).map
        c.action.groupEquiv.toMonoidHom)
      = ((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom).map
          c.action.groupEquiv.toMonoidHom ⊓
        d.second.map c.action.groupEquiv.toMonoidHom := by
          exact Subgroup.map_inf _ _ c.action.groupEquiv.toMonoidHom
            c.action.groupEquiv.injective
    _ = (F₁.prod F₂) ⊓ ((⊥ : Subgroup D).prod ⊤) := by
          rw [Subgroup.map_map]
          rw [← c.second_eq, Subgroup.map_map]
          simp
    _ = (⊥ : Subgroup D).prod F₂ := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxF, hxT⟩
        refine ⟨?_, hxF.2⟩
        exact mem_bot.mp hxT.1
      · intro hx
        refine ⟨⟨(bot_le : (⊥ : Subgroup D) ≤ F₁) hx.1, hx.2⟩,
          ⟨hx.1, mem_top _⟩⟩

/-- The first-coordinate intersection in marked product coordinates. -/
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.map_inf_first
    (c : d.MarkedProduct τ) (F₁ F₂ : Subgroup D) :
    (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.first).map
      c.action.groupEquiv.toMonoidHom) = F₁.prod (⊥ : Subgroup D) := by
  calc
    (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.first).map
        c.action.groupEquiv.toMonoidHom)
      = ((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom).map
          c.action.groupEquiv.toMonoidHom ⊓
        d.first.map c.action.groupEquiv.toMonoidHom := by
          exact Subgroup.map_inf _ _ c.action.groupEquiv.toMonoidHom
            c.action.groupEquiv.injective
    _ = (F₁.prod F₂) ⊓ ((⊤ : Subgroup D).prod ⊥) := by
          rw [Subgroup.map_map]
          rw [← c.first_eq, Subgroup.map_map]
          simp
    _ = F₁.prod (⊥ : Subgroup D) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxF, hxT⟩
        refine ⟨hxF.1, ?_⟩
        exact mem_bot.mp hxT.2
      · intro hx
        refine ⟨⟨hx.1, (bot_le : (⊥ : Subgroup D) ≤ F₂) hx.2⟩,
          ⟨mem_top _, hx.2⟩⟩


/-- The second-coordinate calculation after embedding the marked quotient group
into an ambient group. -/
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.map_subtype_inf_second
    {H : Type*} [Group H] (c : d.MarkedProduct τ) (j : K →* H)
    (hj : Function.Injective j) (F₁ F₂ : Subgroup D) :
    ((F₁.prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) ⊓ d.second.map j) =
      ((⊥ : Subgroup D).prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) := by
  calc
    ((F₁.prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) ⊓ d.second.map j)
      = ((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom).map j ⊓
          d.second.map j := by
            rw [Subgroup.map_map]
    _ = (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓
          d.second).map j) := by
            exact (Subgroup.map_inf _ _ j hj).symm
    _ = ((⊥ : Subgroup D).prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) := by
          have hinter :
              (F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.second =
                ((⊥ : Subgroup D).prod F₂).map
                  c.action.groupEquiv.symm.toMonoidHom := by
            apply (Subgroup.map_injective (f := c.action.groupEquiv.toMonoidHom) c.action.groupEquiv.injective)
            rw [c.map_inf_second, Subgroup.map_map]
            simp
          rw [hinter, Subgroup.map_map]


/-- The first-coordinate calculation after embedding the marked quotient group
into an ambient group. -/
theorem SourceInduction.SourceTwoFactorCase.MarkedProduct.map_subtype_inf_first
    {H : Type*} [Group H] (c : d.MarkedProduct τ) (j : K →* H)
    (hj : Function.Injective j) (F₁ F₂ : Subgroup D) :
    ((F₁.prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) ⊓ d.first.map j) =
      (F₁.prod (⊥ : Subgroup D)).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) := by
  calc
    ((F₁.prod F₂).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) ⊓ d.first.map j)
      = ((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom).map j ⊓
          d.first.map j := by
            rw [Subgroup.map_map]
    _ = (((F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓
          d.first).map j) := by
            exact (Subgroup.map_inf _ _ j hj).symm
    _ = (F₁.prod (⊥ : Subgroup D)).map
        (j.comp c.action.groupEquiv.symm.toMonoidHom) := by
          have hinter :
              (F₁.prod F₂).map c.action.groupEquiv.symm.toMonoidHom ⊓ d.first =
                (F₁.prod (⊥ : Subgroup D)).map
                  c.action.groupEquiv.symm.toMonoidHom := by
            apply (Subgroup.map_injective (f := c.action.groupEquiv.toMonoidHom)
              c.action.groupEquiv.injective)
            rw [c.map_inf_first, Subgroup.map_map]
            simp
          rw [hinter, Subgroup.map_map]

end CFSG.Quasithin.ChapterB
