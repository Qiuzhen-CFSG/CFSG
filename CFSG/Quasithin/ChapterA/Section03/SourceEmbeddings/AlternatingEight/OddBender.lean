module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBenderOdd

/-!
# The Bender containing row for the original A₈ section

Adjoining the original full Sylow to a local C-component gives a nonsolvable
subgroup. In a Bender model every proper full-Sylow overgroup is solvable,
so this join is the whole simple group. The original Sylow normalization
then makes the local component normal and hence equal to the whole group.
The argument keeps its possible nontrivial two-core and does not require
quasisimplicity of the local component.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The literal Sylow-normalized local component fills a simple Bender model. -/
theorem eq_top_of_bender_model (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : ClassificationModels.IsBenderModel G) : B = ⊤ := by
  have htop : B ⊔ (S : Subgroup G) = ⊤ := by
    by_contra hne
    let : Group.IsSolvable (B ⊔ (S : Subgroup G) : Subgroup G) :=
      bender_solvable_proper_sylow_overgroup hm S _ le_sup_right hne
    exact hB.not_isSolvable inferInstance
  have hnB : B.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique (htop ▸ sup_le le_normalizer hn)
  rcases hnB.eq_bot_or_eq_top with hbot | htop
  · have hb : B.subgroupOf (B ⊔ (S : Subgroup G)) = ⊥ := by simp [hbot]
    exact (hB.ne_bot hb).elim
  · exact htop

/-- The odd and Bender containing rows of the original A₈-section application.
The odd rows are impossible; the Bender rows force equality. -/
theorem eq_top_of_odd_or_bender_model (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hm : ChapterA.Section02.IsTheoremCOddModel G ∨ ClassificationModels.IsBenderModel G) :
    B = ⊤ := by
  rcases hm with hodd | hbender
  · exact (not_linearFourTwo_section_of_odd_model hodd B hsection).elim
  · exact eq_top_of_bender_model S B hB hn hbender

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
