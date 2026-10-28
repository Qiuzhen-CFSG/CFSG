module

public import Theory.SpecificGroups.PSL3Four.CentralCover.AutomorphismLifting
public import Theory.GroupTheory.ConjugationFiberProduct.FourKernelComparison

/-! Whole extensions of the perfect four-cover compare once their literal
projective conjugation images agree. Faithfulness on the center and outer
index six make the diagonal fiber quotient split. The resulting equivalence
extends the unique cover comparison, without a simultaneous choice of S₃
complement actions. -/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

/-- Equal projective actor images determine the entire normalizer extension
over the unique prescribed four-cover comparison. -/
theorem FourCover.exists_normalizer_mulEquiv
    (N : Subgroup A) (M : Subgroup B) [N.Normal] [M.Normal]
    (c : FourCover N) (c' : FourCover M)
    (hZC : centralizer ((center N).map N.subtype : Set A) ≤ N)
    (hcM : centralizer (M : Set B) ≤ M)
    (hi : N.index = 6)
    (himage : ((c.toCover.autMap c.ker_eq_center).comp
      (MulAut.conjNormal : A →* MulAut N)).range =
      ((c'.toCover.autMap c'.ker_eq_center).comp
        (MulAut.conjNormal : B →* MulAut M)).range) :
    ∃ (d : N ≃* M) (e : A ≃* B),
      (∀ n, c'.toMonoidHom (d n) = c.toMonoidHom n) ∧
      ∀ n : N, e n = (d n : B) := by
  obtain ⟨d,hd,_⟩ := c.existsUnique_mulEquiv_over c'
  let α := c.toCover.autMap c.ker_eq_center
  let β := c'.toCover.autMap c'.ker_eq_center
  have hact (b : B) : α (ConjugationFiberProduct.action N M d b) =
      β (MulAut.conjNormal b) := by
    ext x
    obtain ⟨n,rfl⟩ := c.surjective x
    change c.toCover.autMap c.ker_eq_center
      (ConjugationFiberProduct.action N M d b) (c.toMonoidHom n) =
      c'.toCover.autMap c'.ker_eq_center (MulAut.conjNormal b) (c.toMonoidHom n)
    rw [c.toCover.autMap_apply,←hd,ConjugationFiberProduct.action_apply]
    rw [←c'.toCover.autMap_apply,hd]
  have heq : (ConjugationFiberProduct.action N M d).range =
      (MulAut.conjNormal : A →* MulAut N).range := by
    apply le_antisymm
    · rintro _ ⟨b,rfl⟩
      have hm : β (MulAut.conjNormal b) ∈
          (α.comp (MulAut.conjNormal : A →* MulAut N)).range := by
        rw [himage]
        exact ⟨b,rfl⟩
      obtain ⟨a,ha⟩ := hm
      exact ⟨a,c.toCover.autMap_injective c.ker_eq_center (ha.trans (hact b).symm)⟩
    · rintro _ ⟨a,rfl⟩
      have hm : α (MulAut.conjNormal a) ∈
          (β.comp (MulAut.conjNormal : B →* MulAut M)).range := by
        rw [←himage]
        exact ⟨a,rfl⟩
      obtain ⟨b,hb⟩ := hm
      exact ⟨b,c.toCover.autMap_injective c.ker_eq_center ((hact b).trans hb)⟩
  let := c.center_isKleinFour
  obtain ⟨e,he⟩ := ConjugationFiberProduct.exists_mulEquiv_of_four_kernel_index_six
    N M d IsKleinFour.card_four hZC hcM hi heq
  exact ⟨d,e,hd,he⟩

end Matrix.PSL3Four
