module

public import Theory.GroupTheory.QuotientPairDirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Composing two dihedral-square factors

Once the two Baumann factor centralizers are assembled as an internal direct
product, their two already-recognized dihedral squares compose to a literal
four-square equivalence.  This lemma carries no extension or source
assumption; it is the final abstract group-theoretic composition.
-/

public section
namespace Theory.GroupTheory

variable {R C₁ C₂ : Type*} [Group R] [Group C₁] [Group C₂]

theorem exists_dihedral_four_product
    (e : R ≃* C₁ × C₂)
    (e₁ : C₁ ≃* (DihedralGroup 4 × DihedralGroup 4))
    (e₂ : C₂ ≃* (DihedralGroup 4 × DihedralGroup 4)) :
    Nonempty (R ≃* (DihedralGroup 4 × DihedralGroup 4) ×
      (DihedralGroup 4 × DihedralGroup 4)) := by
  exact ⟨e.trans (MulEquiv.prodCongr e₁ e₂)⟩

end Theory.GroupTheory
