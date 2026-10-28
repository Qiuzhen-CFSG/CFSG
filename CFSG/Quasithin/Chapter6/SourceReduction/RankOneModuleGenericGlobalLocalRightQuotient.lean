module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightSource
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The exchanged source factor modulo its own two-core

In the exchanged E.2.2 row, the source clauses identify the maximal-subgroup
core with the ambient two-core. The C-component quotient equivalence then
transports the marked PSL₂ or Suzuki model to the component's own two-core
quotient. This uses subnormality and does not require component normality.
An explicit image equivalence avoids rewriting dependent quotient instances.

The final theorem applies the transport to the literal factor C.map H.subtype
selected in G. It supplies the quotient field required by `RightFactor`;
selection, invariance and Borel geometry remain separate obligations. No
identification with the whole residual is made.

Source: Aschbacher--Smith E.2.2(1a), printed pp.215--216, 5.1.10(1), p.634,
and the right-factor selection on p.646 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

private def quotient_image_equiv (C N D : Subgroup X) [N.Normal] [D.Normal]
    (he : N = D) :
    C.map (QuotientGroup.mk' N) ≃* C.map (QuotientGroup.mk' D) := by
  subst D
  exact MulEquiv.refl _

/-- The exchanged source marking identifies the intrinsic two-core quotient,
without assuming that the selected C-component is normal. -/
theorem exchanged_component_quotient {M C U : Subgroup X} {f : ℕ}
    (hC : C.IsCComponent) (hc : ExchangedClauses M C U)
    (hm : ExchangedModel M C f) :
    ChapterF.Source.IsRankOneModel (C ⧸ pCore 2 C) := by
  have hi : ChapterF.Source.IsRankOneModel (sourceImage M C) := by
    rcases hm with hlin | hsuz
    · obtain ⟨F, hF, hfin, hchar, hf, hcard, e, he⟩ := hlin
      exact .linear f (by omega) ⟨F, hF, hfin, hcard, ⟨e⟩⟩
    · obtain ⟨m, hm, hf, e, he⟩ := hsuz
      exact .suzuki m ⟨e⟩
  change ChapterF.Source.IsRankOneModel
    (C.map (QuotientGroup.mk' (sourceKernel M))) at hi
  exact hi.of_equiv ((cComponentTwoCoreQuotientEquiv hC).trans
    (quotient_image_equiv C _ _ hc.kernel_eq).symm)

variable {G : Type*} [Group G] [Finite G]

/-- The actual ambient source factor has the required `RightFactor.quotient`
model. Both subgroup inclusion and its intrinsic two-core are transported. -/
theorem exchanged_source_factor_quotient {T : Sylow 2 G} {L H : Subgroup G}
    {C : Subgroup H} {f : ℕ} (hC : C.IsCComponent)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    ChapterF.Source.IsRankOneModel
      ((C.map H.subtype) ⧸ pCore 2 (C.map H.subtype)) := by
  let e := C.equivMapOfInjective H.subtype H.subtype_injective
  let eq := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)
  exact (exchanged_component_quotient hC hc hm).of_equiv eq.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
