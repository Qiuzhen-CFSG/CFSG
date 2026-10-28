module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases

/-!
# The linear characteristic-two cases with compatible diagram actions

At odd field exponent, the ordinary SL₃ projection is an isomorphism.
Transporting the source recognition through its inverse carries the Borel
and both standard parabolics together, so the same T-induced automorphism
still acts nontrivially on the diagram. The analogous characteristic-two
SL₂ comparison refines the exchanged and single Bender cases. The Suzuki
and unitary models, the literal Sp₄′ convention, and all central kernels
remain in their source quotients H/J.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and 15.3.65, printed p.1152.
-/

@[expose] public section
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
namespace SourceCases

private theorem preservesParabolicClass_map
    {X Y : Type*} [Group X] [Group Y] {a : MulAut X} {P : Subgroup X}
    (φ : X ≃* Y) (h : PreservesParabolicClass a P) :
    PreservesParabolicClass (MulAut.congr φ a) (P.map φ.toMonoidHom) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨φ g, ?_⟩
  have he := congrArg (fun S : Subgroup X => S.map φ.toMonoidHom) hg
  rw [Subgroup.map_map, Subgroup.map_map] at he ⊢
  convert he using 1 <;> congr 1 <;> ext x <;> simp [MulAut.congr]

variable {G : Type*} [Group G]

/-- The same model equivalence transports the nontrivial diagram action to SL₃. -/
theorem MovesDiagram.sl3 {F : Type*} [Field F] [Finite F]
    {H M K T : Subgroup G} {f : ℕ}
    {e : sourceImage H M K ≃* PSL(3,F)}
    (h : MovesDiagram H M K T e (pointParabolic F) (lineParabolic F))
    (hF : Nat.card F = 2 ^ f) (hf : Odd f) :
    MovesDiagram H M K T (e.trans (sl3ProjectiveEquiv hF hf).symm)
      (pointParabolicSL F) (lineParabolicSL F) := by
  obtain ⟨a, ha, hm⟩ := h
  refine ⟨a, ha, ?_⟩
  rintro ⟨hP, hQ⟩
  apply hm
  have he : MulAut.congr (sl3ProjectiveEquiv hF hf)
      (MulAut.congr (e.trans (sl3ProjectiveEquiv hF hf).symm) a) = MulAut.congr e a := by
    ext x
    simp [MulAut.congr]
  have hP' := preservesParabolicClass_map (sl3ProjectiveEquiv hF hf) hP
  have hQ' := preservesParabolicClass_map (sl3ProjectiveEquiv hF hf) hQ
  rw [he] at hP' hQ'
  exact ⟨hP', hQ'⟩
/-- The linear form of the exchanged models, with the same defining field. -/
def LinearExchangedModel (H M K : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    2 ≤ f ∧ Nat.card F = 2 ^ f ∧ ModelBorelPair H M K (BenderSuzuki.Converse.Borel F)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
    ModelBorelPair H M K (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m))

/-- At odd exponent the linear diagram model is SL₃; Sp₄′ is retained literally. -/
def LinearDiagramModel (H M K T : Subgroup G) (f : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage H M K ≃* SL(3,F),
      (componentOverlap H M K).map e.toMonoidHom = borelSL F ∧
      MovesDiagram H M K T e (pointParabolicSL F) (lineParabolicSL F)) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    0 < f ∧ Nat.card F = 2 ^ f ∧
    ∃ e : sourceImage H M K ≃* Sp4Derived F,
      (componentOverlap H M K).map e.toMonoidHom = sp4DerivedBorel F ∧
      MovesDiagram H M K T e
        ((Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)).subgroupOf (Sp4Derived F))
        ((Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)).subgroupOf (Sp4Derived F)))

/-- Replace the faithful characteristic-two PSL₂ projection by its inverse. -/
theorem ExchangedModel.linear {H M K : Subgroup G} {f : ℕ}
    (h : ExchangedModel H M K f) : LinearExchangedModel H M K f := by
  rcases h with ⟨F, hF, hfin, hc, hf, hcard, hB⟩ | h
  · exact Or.inl ⟨F, hF, hfin, hc, hf, hcard, hB.sl2⟩
  · exact Or.inr h

/-- After oddness, transport both the Borel and diagram action through the SL₃ projection. -/
theorem DiagramModel.linear {H M K T : Subgroup G} {f : ℕ}
    (h : DiagramModel H M K T f) (hf : Odd f) : LinearDiagramModel H M K T f := by
  rcases h with ⟨F, hF, hfin, hc, hf0, hcard, e, hB, hd⟩ | h
  · refine Or.inl ⟨F, hF, hfin, hc, hf0, hcard,
      e.trans (sl3ProjectiveEquiv hcard hf).symm, ?_, hd.sl3 hcard hf⟩
    change (componentOverlap H M K).map
      ((sl3ProjectiveEquiv hcard hf).symm.toMonoidHom.comp e.toMonoidHom) = _
    rw [← Subgroup.map_map, hB]
    exact sl3ProjectiveEquiv_borel hcard hf
  · exact Or.inr h

/-- The characteristic-two alternatives with linear matrix identifications.
All models remain images in H/J and all source central kernels are retained. -/
inductive LinearCases (H M K T : Subgroup G) (f : ℕ) : Prop
  | exchanged : ExchangedClauses H M K T → LinearExchangedModel H M K f →
      LinearCases H M K T f
  | bender : SingleClauses H M K T → (LinearExchangedModel H M K f ∨ UnitaryModel H M K f) →
      LinearCases H M K T f
  | diagram : SingleClauses H M K T → LinearDiagramModel H M K T f → LinearCases H M K T f

/-- All three surviving alternatives retain their clauses under the linear comparisons. -/
theorem ReducedCases.linear {H M K T : Subgroup G} {f : ℕ}
    (h : ReducedCases H M K T f) (hf : Odd f) : LinearCases H M K T f := by
  rcases h with ⟨hc, hm⟩ | ⟨hc, hm⟩ | ⟨hc, hm⟩
  · exact .exchanged hc hm.linear
  · exact .bender hc (hm.imp ExchangedModel.linear id)
  · exact .diagram hc (hm.linear hf)
end SourceCases
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
