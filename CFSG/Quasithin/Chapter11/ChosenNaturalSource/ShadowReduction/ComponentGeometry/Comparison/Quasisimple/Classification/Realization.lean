module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Action
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Hyperplane
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Products
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Irreducible test actions for the complete B.5.1 comparison

The irreducible row retains the original moved central section and its
unchanged actor. In each reducible row, the actual linear-group marking
supplies a faithful natural action of the same actor and embedded component.
A full hyperplane centralizer is a best offender on that natural module.
Thus irreducible B.4 obstructions apply to every B.5.1 row, without assuming
the original module is irreducible or discarding its covering center.

Used by CentralQuotients for the negative comparisons in source 11.4.2.
Source: Aschbacher--Smith B.4.2, B.5.1 and 11.4.2, pp.86,99,776--777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open ChapterB.QuasisimpleSource
universe u v

/-- A faithful irreducible FF action of the same actor and embedded component. -/
def HasIrreducibleFFAction (Q : Type u) [Group Q] (K : Subgroup Q) : Prop :=
  ∃ (W : Type v) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
    (_ : FiniteDimensional (ZMod 2) W) (σ : Representation (ZMod 2) Q W),
    Function.Injective σ ∧ IsIrreducible (σ.comp K.subtype) ∧ IsFFModule σ

private theorem natural_realization {Q : Type u} [Group Q] (K : Subgroup Q)
    (F : BinaryField) {n : ℕ} (hn : 2 ≤ n) (hK : K = ⊤)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin n) F.Carrier) :
    HasIrreducibleFFAction.{u,0} Q K := by
  let a : Q ≃* Matrix.SpecialLinearGroup (Fin n) F.Carrier :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr hK).symm).trans e
  let σ := (linearNatural F n).comp a.toMonoidHom
  have ha : ActionEquiv σ (linearNatural F n) :=
    ⟨a,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hb : ActionEquiv (σ.comp K.subtype) (linearNatural F n) :=
    ⟨e,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  refine ⟨(Fin n → F.Carrier),inferInstance,inferInstance,inferInstance,σ,
    (SmallMoved.linearNatural_faithful F n).comp a.injective,
    ExtensionConsequences.irreducible_of_equiv hb
      (ExtensionConsequences.linearNatural_irreducible F hn),?_⟩
  have hff : IsFFModule (linearNatural F n) :=
    ⟨_,(ChapterK.Linear.Natural.hyperplaneCentralizer_best F n ⟨0,by omega⟩ hn).isOffender _⟩
  exact hff.map_equivariant _ _ a.symm.toMonoidHom a.symm.injective
    (LinearEquiv.refl _ _) (fun _ _ => by simp [σ])

/-- Complete B.5.1 supplies a faithful irreducible FF test action without
changing the actor or its embedded component. Reducible rows use their
marked natural representation; the original representation need not split. -/
theorem irreducible_realization_of_source
    {Q : Type u} [Group Q] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hff : IsFFModule ρ) :
    HasIrreducibleFFAction.{u,v} Q K ∨ HasIrreducibleFFAction.{u,0} Q K := by
  cases c.clause_one with
  | irreducible _ hf hi _ _ =>
    refine Or.inl ⟨_,inferInstance,inferInstance,inferInstance,c.sectionData.action,hf,hi,?_⟩
    obtain ⟨A,hA⟩ := hff
    exact ⟨A,IrreducibleBranch.moved_offender c.sectionData hA⟩
  | doubleThree F hK e _ _ =>
    exact Or.inr (natural_realization K F (by decide) hK e.groupEquiv)
  | naturalDual n hn hK e =>
    exact Or.inr (natural_realization K BinaryField.two (by omega) hK e.some.groupEquiv)
  | repeatedNatural n _ hn _ _ hK e =>
    exact Or.inr (natural_realization K BinaryField.two (by omega) hK e.some.groupEquiv)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
