module
public import Theory.GroupAction.IrreducibleCyclicNormal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical.SourceAssembly
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Structure

/-!
# The actual inner-action step for a normal detected component

In H/O₂(H), the original complement remains noncyclic and has irreducible
normalizer action on its literal Frattini quotient. The full outer-model
inspection therefore makes its action on a normal detected component inner.
Genuine Theorems A and C supply the central-quotient model of that component;
no outer-action or automorphism-coverage premise is retained.

Source: Aschbacher–Smith, proof of 1.3.4, printed p.510, invariant-component case.
The later containment of the original complement in the component remains
separate from this inner-action assertion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u

theorem LocalInput.quotient_complement_le_component_centralizer
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal) :
    quotientImage H P ≤ quotientImage H L ⊔
      centralizer (quotientImage H L : Set (XiQuotient H)) := by
  let : Fact p.Prime := ⟨h.prime⟩
  let B := quotientImage H L
  let : IsQuasisimple B := hL.component.2
  let : B.Normal := hn
  have hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hH.stronglyQuasithin, hH.isKGroup.quotient _⟩
  have hB : B.IsCComponent := component_isCComponent hL.component
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical (fittingSubgroup B) inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting hA hC hsq B hB hf).2
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) :=
    h.quotient_normalizer_irreducible
  exact hi.le_sup_centralizer_of_outer h.prime h.odd h.quotient_odd_complement.isPGroup
    h.quotient_complement_not_cyclic B (OuterModels.quasisimple_outer_cyclicNormalOddQuotient hm)

end CFSG.Quasithin.Chapter1.XiEmbedding
