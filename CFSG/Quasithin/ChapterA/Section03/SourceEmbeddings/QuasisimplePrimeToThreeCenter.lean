module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
/-!
# Three-prime centers in quasisimple SQTK groups

Apply the genuine A.3.6 containing-component classification to the whole
quasisimple group with trivial two-core. Its only nonsimple possibilities
have center of order three. A center of order prime to three therefore
forces simplicity. This is used for the original Cartan-containing quotient
in Proposition 9.3.1, after its three-center has been excluded.

Source: Aschbacher--Smith A.3.6, printed pp.43--44.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
/-- The center restriction excludes the genuine central three-cover rows. -/
theorem quasisimple_isSimple_of_center_coprime_three [IsQuasisimple G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (hz : Nat.Coprime 3 (Nat.card (center G))) : IsSimpleGroup G := by
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  obtain ⟨hs,_⟩ | ⟨⟨a⟩,_⟩ := quasisimple_containing_component_models_knownSimple hG hO ht
  · let := hs
    exact (topEquiv (G := G)).symm.isSimpleGroup
  · have hc : Nat.card (center G) = 3 := by
      rw [←Nat.card_congr (centerCongr (topEquiv (G := G))).toEquiv,
        Nat.card_congr a.toEquiv]
      simp
    rw [hc] at hz
    norm_num at hz
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
