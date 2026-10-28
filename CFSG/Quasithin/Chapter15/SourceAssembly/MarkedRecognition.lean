module

public import CFSG.Quasithin.Chapter15.SourceAssembly
public import CFSG.Quasithin.Chapter15.SourceMarkedRecognition.Complete

/-!
# Theorem E composition with source F.6 discharged

The complete marked F.6 recognition supplies the multiple-centralizer
branch of Theorem E. The two original singleton-centralizer arguments,
15.1.3 and15.3.1, remain explicit for their source producers.

Source: Aschbacher--Smith, final proof of Theorem E, printed p.1165.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The final E composition now retains only its two original source
reductions. Corrected F.6 and the Section15.4 branch are proved inputs. -/
theorem source_theoremE_of_original_singleton_reductions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (h1531 : ∀ M Mc : Subgroup G, IsOrderingMaximal T M →
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      NaturalOrthogonalAction M (localModule T M) → False) :
    ClassificationModels.IsTheoremEModel G :=
  source_theoremE_of_original_reductions hG T hempty
    FSource.sourceClassification_knownSimple_complete h1513 h1531

end CFSG.Quasithin.Chapter15
