module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Structure
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# Original SQTK source for the nonnormal-component outer restriction

Genuine earlier Theorems A and C classify the literal central quotient of an
ordinary component. The complete model inspection then makes its outer group
abelian or a two-group. No A.3.8 four-model predicate is required. This is the
exact weaker source consequence consumed by the odd Frattini-commutator action
in Proposition 1.3.4, retaining the full known-simple K-group hypothesis.

Source: Aschbacher–Smith A.3.8(3), pp.45–46; proof of 1.3.4, p.510.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
universe u

/-- The nonnormal-component outer restriction from original SQTK inputs and
complete earlier A/C. Both alternatives give abelian odd-order action. -/
theorem nonnormal_component_outer
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    {G : Type u} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal) :
    IsMulCommutative (MulAut.Outer B) ∨ IsPGroup 2 (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting hA hC hG B
    (Chapter1.XiEmbedding.component_isCComponent hB) hf).2
  exact nonnormal_outer_of_model (hG.stronglyQuasithin 3 (by decide) (by decide))
    hcore B hB hnormal hm

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
