module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidual

/-!
# Containing-component exclusions on the literal chosen residual

The chosen-module normalization supplies the actual Sylow normalization in
the H* argument. The M₂₃ and J₂ rows are excluded unconditionally. The proved
containing catalogue then retains only the J₄ row in a proper
containing C-component. This applies to the embedded residual used by the
original Chapter 12 assembly, without replacement quotient or action data.
The remaining J₄ exclusion and the faithful-signalizer exclusion stay
with the residual maximality/nonfaithfulness owner.

Source: Aschbacher–Smith, 5.1.12 and 5.1.14, printed pp.635 and 638,
as used by 12.2.2 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H Y : Subgroup G} (D : ChosenModule T L V)
include D

/-- No actual normal containing component of the chosen exceptional residual
has M₂₃ as its intrinsic two-core quotient. -/
theorem rankOne_linear_residual_excludes_mathieu23_container
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hHY : H ≤ Y) (C : Subgroup Y) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23) :=
  linear_residual_excludes_mathieu23_container T D.sylow_normalizes_component
    hH hlinear hHY C hRC

/-- The exact unresolved containing rows after the Mathieu exclusion. -/
theorem rankOne_linear_residual_proper_containing_component_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) :=
  linear_residual_proper_containing_component_janko h.simpleQTKE T
    D.sylow_normalizes_component hH hlinear hY C hC hnC hRC hne

omit D in
/-- The J₂ quotient is impossible on every actual containing subgroup of
the chosen exceptional residual. -/
theorem rankOne_linear_residual_excludes_jankoTwo_container
    (_hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hHY : H ≤ Y) (C : Subgroup Y) (hRC : residual H ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  exact linear_residual_excludes_jankoTwo_container hHY C hRC hlinear

/-- Only the actual J₄ quotient survives in a proper containing component.
This is a reduction; excluding that final row remains necessary for maximality. -/
theorem rankOne_linear_residual_proper_containing_component_jankoFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) :=
  linear_residual_proper_containing_component_jankoFour h.simpleQTKE T
    D.sylow_normalizes_component hH hlinear hY C hC hnC hRC hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
