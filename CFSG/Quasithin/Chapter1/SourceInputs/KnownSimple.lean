module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.SourceInputs
/-!
# The original 1.1.5 component action for the full known-simple catalogue

The source A/B/C induction supplies the only remaining classification input
to the already proved marked involution theorem.
Source: Aschbacher--Smith 1.1.5(3).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin
open ChapterA ChapterA.Section02 Chapter1
open Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G]

theorem Chapter1.lemma_1_1_5_three_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G)
    (h : Lemma115Hypotheses H S M z) (D : Subgroup H) (hD : IsComponent H D) :
    D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ ∧ ¬ D.map H.subtype ≤ M ∧
      HasModelAction115 D z :=
  Chapter1.lemma_1_1_5_three_source hG
    (fun X _ _ => theoremsABC_knownSimple (G := X)) H S M z h D hD

end CFSG.Quasithin
