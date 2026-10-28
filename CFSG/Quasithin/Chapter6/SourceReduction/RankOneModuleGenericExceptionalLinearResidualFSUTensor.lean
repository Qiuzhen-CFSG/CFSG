module
public import CFSG.Quasithin.Chapter3.Section02.LinearThreeFourGraphTensor
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualReduction

/-!
# Excluding the Hermitian FSU row for the actual exceptional residual

The nontrivial diagram actor already forced by H* is incompatible with the
literal Hermitian tensor action on the FSU module. This closes that module
row without assuming a chosen graph factor or a T-invariant seed. The final
conditional implication constructs the FSU under faithfulness and applies
this exclusion once recognition of its original module is supplied.

The maximality and recognition premises are not proved here. Their discharge,
including the remaining J₄ embedding and the earlier FSU module alternatives,
stays with qt-d-1222-linear-residual-maximal-nonfaithful. Its final source
assembly is retained by qt-d-1222-rankone-exceptional-linear-analysis.
Source: Aschbacher–Smith 3.2.9(4), pp.582–583, and opening of 5.1.14, p.638
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K : Subgroup G}

/-- The genuine diagram actor excludes the Hermitian row on the literal FSU. -/
theorem linear_four_graph_fsu_not_hermitian
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K)
    (hg : HasLinearFourGraphAction (T : Subgroup G) K) :
    ¬ Nonempty D.HermitianFourMarking := by
  rintro ⟨m⟩
  obtain ⟨F,hF,hfin,hcard,e,t,ht,a,b,ha,hb,hd⟩ := hg
  exact hd (D.hermitianFour_diagram_trivial m hcard e t ht a b ha hb)

/-- Unconditional application to every FSU on the original exceptional residual. -/
theorem linear_residual_fsu_not_hermitian
    {M H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T (residual H)) :
    ¬ Nonempty D.HermitianFourMarking :=
  linear_four_graph_fsu_not_hermitian D (linear_residual_graph_action T hTM hH hlinear)

/-- Tensor recognition would finish nonfaithfulness after maximality. Both
premises remain with this task; no unconditional source theorem is asserted. -/
theorem linear_residual_nonfaithful_of_hermitian_recognition
    {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : ∀ D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H), Nonempty D.HermitianFourMarking) :
    ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) := by
  intro hf
  obtain ⟨D⟩ := linear_residual_fundamentalSetup hG hlinear hmax hf
  exact linear_residual_fsu_not_hermitian hTM hH hlinear D (hmodel D)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
