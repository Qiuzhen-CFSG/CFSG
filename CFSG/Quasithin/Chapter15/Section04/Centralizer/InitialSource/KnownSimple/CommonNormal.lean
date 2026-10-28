module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.SourceResidual
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.CommonNormalKnownSimple

/-!
# The many-overgroup Theorem E branch with common-normal source discharged

The original Chapter 15 argument now consumes the proved known-simple
Theorem 3.1.1 through its exact ratio-source interface. Thus the common-normal
implication is no longer an additional premise. The actual simple QTKE group,
Sylow subgroup, empty faithful-local-component family and multiple maximal
two-local overgroups of the central omega subgroup are preserved.

The remaining classification premises are the genuine Goldschmidt and
corrected F.6 source implications. The independent Section 15.3 branch is
still required for full Theorem E.

Source: Aschbacher–Smith, 15.4.2–25, printed pp.1155–1165.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource

open LocalSetup.TwoFactors
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original many-centralizer-overgroups branch of Theorem E, retaining
only the two genuine amalgam classification inputs. -/
theorem source_many_theoremE_from_amalgam_sources
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G :=
  source_many_theoremE_from_source_residual RatioSource.source_earlier311_knownSimple
    classification sourceF hG T hempty hmany

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
