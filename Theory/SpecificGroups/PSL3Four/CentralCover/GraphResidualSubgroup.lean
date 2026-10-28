module

public import Theory.SpecificGroups.PSL3Four.CentralCover.AutomorphismLifting
public import Theory.SpecificGroups.PSL3Four.CentralCover.MarkedFixedResiduals
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-! The graph automorphism lifts to every actual central four-cover. Its
fixed-subgroup two-residual is an embedded PSL₂(4), hence A₅. The subgroup
is constructed inside the given cover, with the original projection retained.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four
variable {E : Type*} [Group E] [Finite E]

/-- An actual graph residual inside the supplied cover, with its matrix and
five-letter alternating markings. -/
theorem FourCover.exists_graph_residual_subgroup (c : FourCover E) :
    ∃ a : MulAut E,
      (∀ x, c.toMonoidHom (a x) = PSL3.OuterSolvable.graph F (c.toMonoidHom x)) ∧
      let R := (pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype
      Nonempty (R ≃* ProjectiveSpecialLinearGroup (Fin 2) F) ∧
      Nonempty (R ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨a, ha, _⟩ := c.existsUnique_mulEquiv_lifting c (PSL3.OuterSolvable.graph F)
  let γ : MulAut E := a
  let e := ((pResidual 2 γ.fixedSubgroup).equivMapOfInjective
    γ.fixedSubgroup.subtype γ.fixedSubgroup.subtype_injective).symm.trans
      (c.graphResidualEquivOfCompatible γ ha)
  obtain ⟨f⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four card_F
  exact ⟨γ, ha, ⟨e⟩, ⟨e.trans f⟩⟩

end Matrix.PSL3Four
