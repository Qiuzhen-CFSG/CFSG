module

public import Theory.GroupTheory.DihedralFourProduct

/-!
# Abstract assembly of the two zero-center Baumann factors

The source-specific work identifies the two restricted quotient images,
their two natural kernel layers, and the commuting centralizers.  This
consumer records the final assembly once those literal data have been
discharged: the Baumann subgroup is the direct product of its two marked
centralizer subgroups, and the two dihedral-square recognitions compose.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10

variable {R X Y C₁ C₂ K₁ K₂ : Type*}
  [Group R] [Group X] [Group Y]

theorem source_a5_zero_baumann_direct_product_of_factor_data
    (q : R →* X × Y) (C₁ C₂ K₁ K₂ : Subgroup R)
    (F₁ : Subgroup X) (F₂ : Subgroup Y)
    (himage : ∀ r : R, q r ∈ F₁.prod F₂)
    (hker : q.ker = K₁ ⊔ K₂)
    (himg₁ : C₁.map q = F₁.prod ⊥)
    (himg₂ : C₂.map q = (⊥ : Subgroup X).prod F₂)
    (hint₁ : C₁ ⊓ q.ker = K₂)
    (hint₂ : C₂ ⊓ q.ker = K₁)
    (hKdisj : Disjoint K₁ K₂)
    (hcomm : C₁ ≤ centralizer (C₂ : Set R))
    (hfactor₁ : Nonempty (C₁ ≃* (DihedralGroup 4 × DihedralGroup 4)))
    (hfactor₂ : Nonempty (C₂ ≃* (DihedralGroup 4 × DihedralGroup 4))) :
    Nonempty (R ≃* (DihedralGroup 4 × DihedralGroup 4) ×
      (DihedralGroup 4 × DihedralGroup 4)) := by
  obtain ⟨e⟩ := exists_quotient_pair_directProduct_of_factors q C₁ C₂ K₁ K₂
    F₁ F₂ himage hker himg₁ himg₂ hint₁ hint₂ hKdisj hcomm
  obtain ⟨e₁⟩ := hfactor₁
  obtain ⟨e₂⟩ := hfactor₂
  exact exists_dihedral_four_product e e₁ e₂

end CFSG.Quasithin.Chapter10

