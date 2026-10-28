module
public import CFSG.Quasithin.Chapter3.Section02.LinearThreeFourRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualFSUTensor

/-!
# Excluding the irreducible FSU case for the exceptional residual

The genuine diagram actor forced by H* contradicts the Hermitian marking
now derived from irreducibility of the actual component action. SQTK, the
generalized Fitting identification, the quotient marking and the cubic
bound are all proved from the original FSU and multiple-overgroup guard.

The irreducibility premise in the final implication and the separate
maximality assertion remain with qt-d-1222-linear-residual-maximal-nonfaithful.
Final 5.1.14 assembly remains with qt-d-1222-rankone-exceptional-linear-analysis.
No unconditional nonfaithfulness assertion is made here.
Source: Aschbacher–Smith 3.2.5,8,9 and 5.1.14, printed pp.580–583,638
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K : Subgroup G}

/-- Every graph-acting FSU has reducible component action on its actual V. -/
theorem linear_four_graph_fsu_not_irreducible
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hg : HasLinearFourGraphAction (T : Subgroup G) K) :
    letI := D.module_elementary
    ¬ Representation.IsIrreducible (D.joinRepresentation.comp D.componentActionImage.subtype) := by
  intro hi
  have hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
    obtain ⟨F,hF,hfin,hcard,e,_⟩ := hg
    exact ⟨F,hF,hfin,hcard,⟨e⟩⟩
  exact linear_four_graph_fsu_not_hermitian D hg
    (D.hermitianFourMarking_of_irreducible hmany hn hlinear hi)

/-- The original H* residual supplies the graph actor unconditionally. -/
theorem linear_residual_fsu_not_irreducible
    {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T (residual H)) :
    letI := D.module_elementary
    ¬ Representation.IsIrreducible (D.joinRepresentation.comp D.componentActionImage.subtype) :=
  linear_four_graph_fsu_not_irreducible D hmany
    (hH.1.1.2.trans (le_normalizer_residual H))
    (linear_residual_graph_action T hTM hH hlinear)

/-- Maximality and source irreducibility would finish residual nonfaithfulness. -/
theorem linear_residual_nonfaithful_of_fsu_irreducible
    {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hi : ∀ D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), letI := D.module_elementary
        Representation.IsIrreducible (D.joinRepresentation.comp D.componentActionImage.subtype)) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) := by
  intro hf
  obtain ⟨D⟩ := linear_residual_fundamentalSetup hG hlinear hmax hf
  exact linear_residual_fsu_not_irreducible hTM hmany hH hlinear D (hi D)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
