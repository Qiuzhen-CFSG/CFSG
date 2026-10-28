module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidualEmbedding

/-!
# The literal exceptional residual in the native J₄ local geometry

The checked containing catalogue and native quotient action give a surjection
from the original local overgroup onto J₄. Its restriction to the containing
component is the specified intrinsic two-core quotient. The original residual
maps to a local component normalized by the full image Sylow, and the original
diagram actor survives. Its nontrivial two-core gives a common two-local,
whose order is prime to 23 by the native Mathieu-local exclusion.

This is the remaining-case reduction in the opening of 5.1.14. The other J₄
local cases and the FSU diagram exclusion still require proof; this module
does not assert maximality or nonfaithfulness. Final assembly remains with
the residual maximality/nonfaithfulness owner.

Source: Aschbacher–Smith A.3.12, 5.1.12 and 5.1.14, printed pp.47–48,
635 and 638, as used by 12.2.2 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterA.Section03
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H Y : Subgroup G} (D : ChosenModule T L V)
include D

/-- The native J₄ configuration forced by any proper containing component
of the original chosen exceptional residual. All quotient and action data
are constructed from the original hypotheses. -/
theorem rankOne_linear_residual_proper_container_jankoFour_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    ∃ (e : (C ⧸ pCore 2 C) ≃* Janko4.Model)
      (f : Y →* Janko4.Model) (P : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ c : C, f c = e (QuotientGroup.mk' (pCore 2 C) c)) ∧
      (P : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      ((residual H).subgroupOf Y).map f ∈ localCComponents P ∧
      (P : Subgroup Janko4.Model) ≤
        normalizer (((residual H).subgroupOf Y).map f : Set Janko4.Model) ∧
      HasLinearFourGraphAction (P : Subgroup Janko4.Model)
        (((residual H).subgroupOf Y).map f) ∧
      pCore 2 (((residual H).subgroupOf Y).map f) ≠ ⊥ ∧
      ∃ N : Subgroup Janko4.Model, IsTwoLocal N ∧
        ((residual H).subgroupOf Y).map f ≤ N ∧
        (P : Subgroup Janko4.Model) ≤ N ∧ ¬ 23 ∣ Nat.card N :=
  linear_residual_proper_container_jankoFour_configuration h.simpleQTKE T
    D.sylow_normalizes_component hH hlinear hY C hC hnC hRC hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
