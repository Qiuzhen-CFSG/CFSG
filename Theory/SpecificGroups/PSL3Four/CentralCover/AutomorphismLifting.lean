module

public import Theory.SpecificGroups.PSL3Four.CentralCover.Uniqueness

/-! The unique four-cover comparison also lifts every automorphism of the
actual projective quotient. It intertwines any actions with the same descent,
as needed to compare the split noncentral-four normalizers in source 44.2. -/

public noncomputable section
open Subgroup PerfectCentralCovering
namespace Matrix.PSL3Four
variable {E E' : Type*} [Group E] [Group E']

private def rebase (c : FourCover E) (β : MulAut PSL) : FourCover E where
  toMonoidHom := β.symm.toMonoidHom.comp c.toMonoidHom
  surjective := β.symm.surjective.comp c.surjective
  isPerfect := c.isPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ β.symm.injective]
    exact c.ker_le_center
  ker_eq_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ β.symm.injective]
    exact c.ker_eq_center
  center_isKleinFour := c.center_isKleinFour

/-- Every projective automorphism lifts uniquely between the given actual
four-covers, preserving the prescribed quotient automorphism. -/
theorem FourCover.existsUnique_mulEquiv_lifting
    (c : FourCover E) (c' : FourCover E') (β : MulAut PSL) :
    ∃! e : E ≃* E', ∀ x, c'.toMonoidHom (e x) = β (c.toMonoidHom x) := by
  obtain ⟨e,he,hu⟩ := c.existsUnique_mulEquiv_over (rebase c' β)
  refine ⟨e,?_,?_⟩
  · intro x
    apply β.symm.injective
    exact (he x).trans (β.symm_apply_apply _).symm
  · intro e' he'
    apply hu e'
    intro x
    change β.symm (c'.toMonoidHom (e' x)) = c.toMonoidHom x
    rw [he',β.symm_apply_apply]

/-- Descent identifies the automorphism group of the actual four-cover with
the entire projective automorphism group. -/
theorem FourCover.autMap_bijective (c : FourCover E) :
    Function.Bijective (c.toCover.autMap c.ker_eq_center) := by
  refine ⟨c.toCover.autMap_injective c.ker_eq_center,?_⟩
  intro β
  obtain ⟨a,ha,_⟩ := c.existsUnique_mulEquiv_lifting c β
  refine ⟨a,?_⟩
  ext x
  obtain ⟨y,rfl⟩ := c.surjective x
  rw [c.toCover.autMap_apply,ha]

/-- The unique cover comparison intertwines the actual lifted actions
whenever their projective descents agree. -/
theorem FourCover.exists_equivariant_mulEquiv
    (c : FourCover E) (c' : FourCover E') {B : Type*} [Group B]
    (ρ : B →* MulAut E) (ρ' : B →* MulAut E') (β : B →* MulAut PSL)
    (hρ : ∀ b x, c.toMonoidHom (ρ b x)=β b (c.toMonoidHom x))
    (hρ' : ∀ b x, c'.toMonoidHom (ρ' b x)=β b (c'.toMonoidHom x)) :
    ∃ e : E ≃* E', (∀ x, c'.toMonoidHom (e x)=c.toMonoidHom x) ∧
      ∀ b x, e (ρ b x)=ρ' b (e x) := by
  let := c.isPerfect
  obtain ⟨e,he,_⟩ := c.existsUnique_mulEquiv_over c'
  refine ⟨e,he,?_⟩
  intro b
  have hh : e.toMonoidHom.comp (ρ b).toMonoidHom =
      (ρ' b).toMonoidHom.comp e.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq c'.toMonoidHom c'.ker_le_center
    ext x
    change c'.toMonoidHom (e (ρ b x))=c'.toMonoidHom (ρ' b (e x))
    rw [he,hρ,hρ',he]
  exact DFunLike.congr_fun hh

end Matrix.PSL3Four
